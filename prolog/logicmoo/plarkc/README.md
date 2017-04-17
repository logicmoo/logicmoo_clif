KE Text
=======

see <https://github.com/TeamSPoon/PrologMUD/blob/master/runtime/try_logicmoo_examples.pl>

The *KE Text* facilities allow authors to compose a set of KB changes in text and add them to a [Cyc KB](Cyc_KB "wikilink") in a single batch operation.

E-Mail Comments to: info@cyc.com.

CopyrightÂ© 1996 â€“ 2015 Cycorp. All rights reserved.

\_\_TOC\_\_

Introduction
------------

KE Text (Knowledge E Text, where the E stands for Editing, which is historically correct, or Entry, which is intuitively correct) is an ASCII text format for specifying changes to a [Cyc KB](Cyc_KB "wikilink"). The text is parsed into KB operations ([asserts](Cyc-Assert "wikilink"), [unasserts](Cyc-Unassert "wikilink"), [renames](Cyc-Rename "wikilink"), etc.) that are then evaluated using the [KE API](KE_API "wikilink") ([ke-assert](ke-assert "wikilink"), [ke-unassert](ke-unassert "wikilink"), [ke-rename](ke-rename "wikilink"), etc.) KE Text is processed through the browser through either the [Load KE File](Load_KE_File "wikilink") page, which loads a KE Text file or the [Compose KE Text](Compose_KE_Text "wikilink") page, which allows typing in KE Text.

The KE Text facilities allow authors to compose a set of KB changes in text and add them to a Cyc KB in a single batch operation. Choosing to use KE Text is strictly a matter of convenience. Operations entered using KE Text do not differ in the KB from those entered via other browser tools. Most users find it convenient in situations where many similar changes need to be made or when they are adding a related set of new constants and assertions.

KE Text Syntax
--------------

KE Text syntax is just a syntactic/notational variation of [CycL](CycL "wikilink"). Many people find it easier and faster to write some types of CycL expressions using KE Text syntax than using â€œcanonicalâ€ [FOPC-in-Lisp](FOPC-in-Lisp "wikilink") CycL syntax, which partly explains why KE Text syntax continues to be supported by knowledge entry tools.

-   Notation
-   Expressions
-   Directives
-   Comments in KE Text
-   Order of Expressions
-   Another Example
-   Processing KE Text in the Cyc Web Interface
-   Loading a KE Test File from a Console Interactor

### Notation

#### Variables

Variables occurring anywhere in a KE text (e.g., inside rule statements) must begin with a question mark (?). This convention signals the knowledge entry facilities to treat the object as a variable, rather than as a constant.

#### Constants

It is not necessary to include the initial â€œ\#$â€ in references to known constants (i.e., constants which Cyc already knows to exist), though it is not disallowed. For example, one could use either [\#$Siegel](#$Siegel "wikilink") or [Siegel](Siegel "wikilink"); [\#$KeithsHouse](#$KeithsHouse "wikilink") or [KeithsHouse](KeithsHouse "wikilink"). Accepted practice is to write KE text without the â€œ\#$â€ prefix.

#### Strings

Strings referred to in KE text (such as entries on the [\#$comment](#$comment "wikilink") predicate for a constant) must be delimited by double quotes (e.g., â€œThis is a string.â€), as in [ Common Lisp](COMPUTER_LANGUAGE_COMMON_LISP "wikilink") and [ C](COMPUTER_LANGUAGE_C "wikilink").

To use double quotes inside comments, prefix them with a backslash. (e.g. â€œThis comment \\â€contains\\â€ double quotes.â€)

KE File preserves tab and return/newline/linefeed characters that occur inside strings, but will remove any non-printing characters.

#### Keywords

Keywords occurring in formulas must be prefixed with a colon.

(e.g. â€œf: ([genKeyword](genKeyword "wikilink") [PublicConstant](PublicConstant "wikilink") :PUBLIC-CONSTANT).â€)

#### Symbols

Symbols occuring in formulas must be prefixed with a single quote.

(e.g. â€œf: ([afterAdding](afterAdding "wikilink") [genls](genls "wikilink") â€˜[GENLS-AFTER-ADDING](GENLS-AFTER-ADDING "wikilink")).â€)

### Expressions

A complete, meaningful syntactic unit of Cyc KE text is an â€œexpressionâ€.

Expressions in KE Text syntax are somewhat analogous to sentences in a natural language, or more closely, to expressions in a programming language such as [Lisp](COMPUTER_LANGUAGE_COMMON_LISP "wikilink") or [Java](COMPUTER_LANGUAGE_JAVA "wikilink"). In [Java](COMPUTER_LANGUAGE_JAVA "wikilink"), the end of an expression is indicated by a semi-colon (;). In [Lisp](COMPUTER_LANGUAGE_COMMON_LISP "wikilink"), the end of an expression is indicated by a right parenthesis that balances a corresponding left parenthesis. In KE Text syntax, each expression must end with a period (.), and the period must be outside a comment or a string. The general form of an expression in KE Text syntax is as follows:

     <directive>: <data-object-or-object-sequence>. 

### Directives

There are two types of objects which may fill the position in a KE text expression: reserved words and predicates.

-   Reserved Words
-   Predicate Directives
-   Special Handling for [TheAssertionSentence](TheAssertionSentence "wikilink")

#### Reserved Words

The first type comprises reserved words (analogous to reserved words in a programming language), which are as follows:

-   Constant
-   In Mt
-   Default Mt
-   Truth Value (or TV)
-   Direction (or D)
-   Formula
-   Enter
-   Delete
-   Rename
-   Kill
-   Include

##### General

The syntax for all reserved words except Enter, Delete, and Rename is the same. Each reserved word is followed by a colon delimiter, exactly one data object, and a period. That is, the form of a reserved word expression in KE Text syntax is:

       <reserved-word>: <data-object>.

Note that reserved word directive names are not case-sensitive. For example, â€œconstantâ€ works just as well as â€œConstantâ€.

##### Enter and Delete

Enter and Delete have the following syntax:

      <reserved-word>. 

##### Rename

Rename has the following syntax:

       <reserved-word> <old-constant-name> .

##### Constant

If the reserved word is â€œConstantâ€, the data object following the colon delimiter must be the name of a Cyc constant (e.g., Pittman, or MarksHouse, or some other Cyc constant). For example:

        Constant: Pittman.
        Constant: Muffet.

If the data object following the colon delimiter is not already known (by Cyc) to be a Cyc constant, users will be asked whether they want to create a new constant with that name.

When an expression beginning with a Constant directive is evaluated, it causes the default entry constant (the â€œcurrentâ€ constant) to be set to the named constant, the default truth value to be set to :unknown, the default direction to also be set to :unknown, and the default entry [microtheory](microtheory "wikilink") to be set to the [BaseKB](BaseKB "wikilink"). The only exception to this is if the [microtheory](microtheory "wikilink") has previously been set via the Default Mt directive, in which case the use of the Constant directive leaves the microtheory unchanged. All of the settings made by the *Constant* directive persist until they are changed by some other (implicit or explicit) directive.

##### In MT

If the reserved word is â€œIn Mtâ€, the data object following the colon delimiter must be a known (i.e., already existing) microtheory.

Example:

    In Mt: HumanActivitiesMt.

When an expression beginning with an In Mt directive is evaluated, it causes the default entry microtheory to be set to the named microtheory. This setting persists until the next occurrence of an *In Mt* directive, a *Default Mt* directive, or a *Constant* directive.

#### Default MT

If the reserved word is â€œDefault Mtâ€, the data object following the colon delimiter must be a known (i.e., already existing) microtheory.

For example:

    Default Mt: HumanActivitiesMt.

When an expression beginning with a Default Mt directive is evaluated, is causes the entry/delete microtheory to be set to the named microtheory. This setting persists until the next occurrence of a Default Mt or In Mt directive, or the end of the file/text being processed. Once a directive has been overriden by another directive, the scope of the original directive is no longer valid, even if the second directive is itself overriden later. Note that this directive, unlike the In Mt directive, prevents each occurrence of a Constant directive from resetting the default microtheory to BaseKB. This directive makes it easier to process all (or most) of the expressions in a file/text segment in the same microtheory.

#### Truth Value

If the reserved word is â€œTruth Valueâ€ (or â€œTVâ€), the data object following the colon delimiter must be one of the keywords :default, :monotonic, or :unknown. (Itâ€™s also OK to omit the colon).

(Check the glossary for a quick description of the difference between default true and monotonically true.)

Examples:

    Truth Value: :monotonic.
     TV: monotonic.

It should only very rarely be necessary for a user to use a Truth Value directive. KE Text assigns truth values to entry expressions automatically. If an entry expression begins with a predicate which is an instance of [DefaultMonotonicPredicate](DefaultMonotonicPredicate "wikilink") (including [isa](isa "wikilink") and [genls](genls "wikilink")), the expression is automatically assigned a truth value of :monotonic. All other entry expressions are automatically assigned a truth value of :default. Note that the strength of â€œimpliesâ€ is :default, by default.The only reason to use a Truth Value directive is if you want to override these built-in defaults.

When an expression beginning with a Truth Value directive is evaluated, it causes the entry truth value for the following expression to be set to the indicated truth value. (Note that an expression might comprise several assertions. This will be explained more fully below). After the expression to be entered is evaluated, the setting immediately reverts to :unknown, until the next entry expression is encountered (and the truth value is automatically set to :default or :monotonic), or until another Truth Value directive is read.

When would you want to use this directive? Suppose you wanted to enter a rule with a truth value of :monotonic. Since the default setting for rules is :default, in your KE text you would want to precede the rule with this expression:

    Truth Value: :monotonic.

#### Direction

If the reserved word is â€œDirectionâ€ (or â€œDâ€), the data object following the colon delimiter must be one of the keywords :forward (to indicate forward propagation), :backward (to indicate backward propagation), or :unknown. (Itâ€™s also OK to omit the colon).

Examples:

     Direction: :forward.
     d: backward.

KE Text assigns directions to entry expressions automatically. Expressions beginning with a simple predicate ([ground atomic formulas](ground_atomic_formula "wikilink")) are assigned a direction of :forward. All other entry expressions (most notably, all rules are assigned a direction of :backward.

The only reason to use a *Direction* directive is if you want to override these built-in defaults.

When an expression beginning with a *Direction* directive is evaluated, it causes the direction for the 'following' entry expression to be set to the indicated direction. After the expression to be entered is read, the setting immediately reverts to :unknown, until the next entry expression is encountered or another Direction directive is read.

The most common use for this directive is to enter rules with a direction of :forward.

#### Formula

If the reserved word is â€œ*F*â€ (for â€œ*formula*â€), the data object following the colon delimiter must be a well-formed CycL Formula.

The constants referred to in the CycL formula must already be known to Cyc (i.e., must already exist, perhaps as a result of being created at some previous point in the KE text).

(KE Text will also accept the directive â€œ*EL*â€ to specify a [CycL Formula](CycL_Formula "wikilink"). â€œ*EL*â€ stands for â€œ*Epistemological Level*â€, as distinct from â€œ*HL*â€, which stands for â€œ*Heuristic Level*â€.)

Examples:

    F: (implies

    (isa ?cat Tiger)

    (hasVisibleSurfacePatternType ?cat StripedPattern)).

    F:  (holdsIn (Year 1995) (owns Goolsbey KeithsHouse)).

    F: (likesAsFriend SimoneSiegel KathyBurns).

#### Enter

If the reserved word is â€œ**Enter**â€, it must be followed by a period. All of the expressions following this reserved word until an occurrence of the reserved word â€œDeleteâ€ (or the end of the file/text) will be processed assuming that the resulting assertions should be entered into the Cyc KB.

For example:

    Enter.
     F : (holdsIn (Year 1995) (owns Goolsbey KeithsHouse)).

The default processing mode for the KE Text facilities (KE File, Compose) is entry mode, so you donâ€™t have to use this reserved word unless you want to start entering assertions after a region of text in which the processing mode was set to delete (see below).

#### Delete

If the reserved word is â€œDeleteâ€, it must be followed by a period. All of the expressions following this reserved word until an occurrence of the reserved word â€œEnterâ€ (or the end of the file/text) will be processed assuming that the resulting assertions should be removed from the Cyc KB.

For example:

    Delete.

    F: (holdsIn (Year 1996) (owns Goolsbey KeithsOldCar)).

    Enter.

    F: (holdsIn (Year 1996) (owns Goolsbey KeithsNewCar)).

Since the default processing mode for the KE Text facilities (KE File, Compose) is entry mode, you must use use the â€œDeleteâ€ reserved word if you want to remove assertions from the Cyc KB by processing KE Text. If the assertion to be removed is a local assertion, the method (FI function) used is KE-UNASSERT. If the assertion to be removed is a remote assertion, the method used is KE-BLAST. Exercise caution in using this directive.

#### Rename

If the reserved word is â€œRenameâ€, the colon delimiter must be followed by a constant name, a string indicating the new name, and a period.

For example:

    Rename: NicksFirstKid â€œSimoneSiegelâ€.

The Rename directive provides a convenient way to do a batch of constant renames in a file/text.

A renamed constant does not become the â€œcurrentâ€ constant.

#### Kill

If the reserved word is â€œKillâ€, the colon delimiter must be followed by the name of the constant to be killed.

For example:


    Kill: highestVolcanoInRegion.

#### Include

If the reserved word is â€œIncludeâ€, the colon delimiter must be followed by the name of the file to be included in quotes.

For example:

    Include: â€œanother-file.keâ€.

The above line will look for the file named another-file.ke in the same directory as the KE Text file being loaded. If the KE Text is being typed into a compose window, you can use the absolute path to the file you want to include. For example:

    Include: â€œ/home/user5/ke/another-file.keâ€.

### Predicate Directives

The second type of directive comprises Cyc predicates occurring within the scope of a (previously occurring) Constant directive. The Constant directive sets the â€œcurrentâ€ constant, which then is understood to be the first argument to assertions generated from the following predicate directive expressions.

(Note that predicate directive names, unlike reserved word directive names, are case-sensitive. After all, a predicate directive name is just the name of a CycL predicate, and CycL constant names are case-sensitive.)

Each predicate directive is followed by a colon delimiter, one or more data objects, and a period. That is, the form of a predicate expression in KE Text syntax is

<predicate>: <data-object-1> \[<data-object-2>â€¦<data-object-n>\].

The data objects following the colon delimiter comprise the additional argument(s) to the predicate in the predicate directive.

Example:

Constant: Goolsbey.

isa: HumanCyclist ElectricalEngineer.

feelsTowardsObject: (SimoneSiegel Affection Positive)

(BillJ Curiosity Positive).

comment: â€œKeith Goolsbey is a member of the Cycorp technical board.â€.

In this example, the Constant directive sets the â€œcurrentâ€ constant to be Goolsbey. Goolsbey is then assumed to be the first argument to assertions formed from the three following predicate directive expressions (the expressions which begin with â€œisaâ€, â€œfeelsTowardsObjectâ€, and â€œcommentâ€).

If the predicate directive is the name of a binary predicate (such as isa and comment), each of the data objects following the colon delimiter is assumed to be part of an assertion in which the predicate directive is the predicate, the default constant is the first argument, and the data object is the second argument.

If the predicate directive is the name of an n-ary predicate where n is greater than 2 (such as \#$feelsTowardsObject), each of the data objects following the colon delimiter must be a list. The elements in the list are assumed to be part of an assertion in which the predicate directive is the predicate, the default constant is the first argument, and the elements (in listed order) are the remaining arguments. So, when evaluated and processed, the KE text fragment in the example above would result in the addition of the following six assertions to the KB:

(\#$isa \#$Goolsbey \#$HumanCyclist)

(\#$isa \#$Goolsbey \#$ElectricalEngineer)

(\#$feelsTowardsObject \#$Goolsbey \#$SimoneSiegel \#$Affection \#$Positive)

(\#$feelsTowardsObject \#$Goolsbey \#$BillJ \#$Curiosity \#$Positive)

(\#$comment \#$Goolsbey â€œKeith Goolsbey is a member of the Cycorp technical board.â€)

Note that because any number of data objects may follow a colon delimiter preceded by a predicate directive, one KE text expression may result in several assertions being added to the knowledge base. Any reserved word directive immediately preceding such a compound KE text expression (i.e., an expression yielding more than one assertion) will apply to all of the assertions resulting from the expression.

Also, note that since a â€œcanonicalâ€ CycL Formula can be entered in KE text by using the F directive, the assertions resulting from the expressions in the example above are exactly the same as the assertions resulting from the expressions in the example immediately below.

Example:


    F: (isa Goolsbey HumanCyclist).

    F: (isa Goolsbey ElectricalEngineer).

    F: (feelsTowardsObject Goolsbey SimoneSiegel Affection Positive).

    F: (feelsTowardsObject Goolsbey BillJ Curiosity Positive).

    F: (comment Goolsbey â€œKeith Goolsbey is a member of the Cycorp technical board.â€).

If Cyc had the unary predicate â€œdogâ€, indicating membership in the class of all dogs (or the quality of â€œdognessâ€), assertions using this predicate could be entered with an expression such as this:

    dog: Brandy .

    F: (dog Brandy) .

### Special Handling for [TheAssertionSentence](TheAssertionSentence "wikilink")

The constant [TheAssertionSentence](TheAssertionSentence "wikilink") has special support for referring to the previously asserted sentence, not including previous sentences that mentioned [\#$TheAssertionSentence](#$TheAssertionSentence "wikilink") itself. This is useful for making meta-assertions without having to copy the [\#$ist](#$ist "wikilink") assertions formula multiple times.

For example:

`;;Â anÂ exampleÂ rule:`
**`In` `Mt`**`:Â `[`BaseKB`](BaseKB "wikilink")`.`
**`f`**`:Â (`[`implies`](implies "wikilink")
`Â Â Â Â Â Â (`[`and`](and "wikilink")
`Â Â Â Â Â Â Â Â Â Â Â Â Â (`[`termOfUnit`](termOfUnit "wikilink")`Â ?NARTÂ (?FUNCÂ .Â ?ARGS))`
`Â Â Â Â Â Â Â Â Â Â Â Â Â (`[`argIsa`](argIsa "wikilink")`Â ?FUNCÂ ?NÂ ?COL)`
`Â Â Â Â Â Â `
`Â Â Â Â Â Â Â Â Â Â Â Â Â (`[`argN`](argN "wikilink")`Â ?ARGNÂ ?NÂ ?NART)`
`Â Â Â Â Â Â Â Â Â Â Â Â Â (`[`isa`](isa "wikilink")`Â ?ARGNÂ `[`Collection`](Collection "wikilink")`))`
`Â Â (`[`isa`](isa "wikilink")`Â ?ARGNÂ ?COL)).`
`Â Â ;;Â assertÂ aÂ `[`ruleTrivialForJustificationParaphrase`](ruleTrivialForJustificationParaphrase "wikilink")`Â `[`GAF`](GAF "wikilink")`Â aboutÂ theÂ rule`
`Â `**`In` `Mt`**`:Â `[`BaseKB`](BaseKB "wikilink")`.`
`Â `**`f`**`:Â (`[`ruleTrivialForJustificationParaphrase`](ruleTrivialForJustificationParaphrase "wikilink")`Â `[`TheAssertionSentence`](TheAssertionSentence "wikilink")`).`
`Â ;;Â assertÂ aÂ `[`salientAssertions`](salientAssertions "wikilink")`Â `[`GAF`](GAF "wikilink")`Â aboutÂ theÂ ruleÂ (notÂ aboutÂ the`
`Â ;;Â Â ruleTrivialForJustificationParaphraseÂ GAF`
`Â `**`In` `Mt`**`:Â `[`BaseKB`](BaseKB "wikilink")`.`
`Â `**`f`**`:Â (`[`salientAssertions`](salientAssertions "wikilink")`Â `[`argIsa`](argIsa "wikilink")`Â `[`TheAssertionSentence`](TheAssertionSentence "wikilink")`).`

Note that this support breaks the ability to make assertions about [TheAssertionSentence](TheAssertionSentence "wikilink") itself using [KE Text](KE_Text "wikilink").

### Comments in KE Text

Comments (text to be read by a human, but not interpreted or entered by a program) are allowed in KE text. The comment indicator is the semi-colon (;), as in Common Lisp. Lines beginning with a semi-colon will be ignored. More precisely, any sequence of characters following a semi-colon (and including the semi-colon) up until the next occurrence of a return (line-break, line-feed) character will be ignored, except when the semi-colon occurs inside a string (a character sequence delimited by double quotes) which is not itself inside a comment.

### Order of Expressions

Expressions in KE text are evaluated and processed in the order of their occurrence in the text. In general, itâ€™s a good idea to write KE text expressions about a constant only after the point where a Constant directive for that constant occurs (unless, of course, the constant is already known to Cyc).

### Another Example

    Constant: Siegel.

    isa: HumanCyclist CulturalAnthropologist.

    In Mt: NaiveBiologicalDescentMt.

    children: SimoneSiegel.

    In Mt: LanguageAndWritingSystemMt.

    Direction: :forward.

    F: (implies

           (languageSpoken ?person EasternPahariLanguage)

           (likesAsFriend Siegel ?person)).

Evaluation of the expressions above would result in the four assertions being added to the Cyc KB.

In the BaseKB, we would have:

    (#$isa #$Siegel #$HumanCyclist)

    (#$isa #$Siegel #$CulturalAnthropologist)

In the NaiveBiologicalDescentMt, we would have:

    (#$children #$Siegel #$SimoneSiegel)

And in the LanguageAndWritingSystemMt, with direction :forward (forward propagation), we would have:

    (#$implies

           (#$languageSpoken ?person #$EasternPahariLanguage)

           (#$likesAsFriend #$Siegel ?person))

### Processing KE Text in the Cyc Web Interface

The Cyc Web Interface provides two facilities for processing KE Text: the Compose page and KE-File. Both may be accessed from the â€œKE-Fileâ€ section of the Cyc Navigator page. The Compose page can also be accessed from the Tools menu.

On the Compose page, you compose KE Text expressions in a large input pane. Clicking the â€œEvalâ€ button submits the completed expressions for processing.

On the KE-File page, you enter the pathname of the KE Text format file that you want to process. Clicking the â€œLoadâ€ button loads the file. The file must be in the filesystem of the Cyc Server Machine.

Either way, the KE Text Parser will process your KE Text and present its results to you before making any changes to the KB.

If it finds syntactic errors in your expressions, it will ask you to correct them before proceeding.

If it finds that you have referred to constants which do not yet exist, it will ask you whether you want to create them.

When the KE Text expressions parse without error or question, it will display the proposed changes as FI operations and ask for confirmation.

If the changes are confirmed, the operations are queued for processing on the Cyc Server Machine.

### Loading a KE Test File from a Console Interactor

To process a KE Text file from a console interactor pane, call the function LOAD-KE-TEXT-FILE.

(In a Lisp implementation of Cyc, make sure you have set the package to â€œcycâ€ by evaluating (in-package â€œcycâ€) before calling LOAD-KE-TEXT-FILE).

`LOAD-KE-TEXT-FILEÂ takesÂ fourÂ arguments:`

-   The first is the userâ€™s Cyc constant name (a character string delimited by double quotes).
-   The second is the pathname of the file to be entered (another character string).
-   The third indicates where the request should be queued, either :agenda, :aux, or NIL.
-   The fourth specifies whether there will be â€œno user interactionâ€. T means no user interaction; NIL indicates there will be user interaction. This argument defaults to NIL.

Unless the fourth argument is T, the user will be asked questions as the file is processed. The user is given the opportunity to preview and confirm the batch of assertions before they are queued for processing.

Appendix A: KE Text History
===========================

KE Text syntax is just a syntactic/notational variation of [CycL](CycL "wikilink"). To some extent, it is a holdover from when Cyc was a frame-based system and CycL was a [frame-based](frame-based "wikilink") language. Many people find it easier and faster to write some types of CycL expressions using KE Text syntax than using â€œcanonicalâ€ [FOPC](FOPC "wikilink")-in-Lisp CycL syntax, which partly explains why KE Text syntax continues to be supported by knowledge entry tools.

`ThereÂ areÂ someÂ aliasesÂ forÂ directivesÂ whichÂ areÂ retainedÂ forÂ backwardÂ compatibilityÂ withÂ filesÂ writtenÂ forÂ olderÂ versionsÂ ofÂ KEÂ Text:`

    Unit = Constant
     Access Level or AL = Direction
     0 = :forward
     4 = :backward
     EL = Formula

In the past you could not include references to a constant in a file/text if the constant appears in a kill expression earlier in the file/text. This would cause problems when the resulting kill expressions are processed by the Cyc Agenda, since the following expressions would reference what is now a dead (non-existent) constant.

Appendix B: KE Text Syntax
--------------------------

    {ke-file}         ::= â€œâ€

    | {full-expression}

     | {full-expression} {ke-file}

     {full-expression} ::= {expression} â€œ.â€

    {expression}      ::= {directive}

     | {predicate-assertion}


     {directive} ::= {assert-mode-directive}

     | {constant-directive}

     | {in-mt-directive}

     | {default-mt-directive}

     | {assertion-direction-directive}

     | {assertion-truth-directive}

     | {include-ke-file-directive}

     | {kill-directive}

     | {rename-directive}

     | {formula-directive}



     {assert-mode-directive} ::= {enter-directive} | {delete-directive}

     {enter-directive} ::= {enter-keyword}

     {enter-keyword} ::= â€œenterâ€



    {delete-directive} ::= {delete-keyword}

     {delete-keyword} ::= â€œdeleteâ€



    {in-mt-directive} ::= {in-mt-keyword} â€œ:â€ {microtheory}

     {in-mt-keyword} ::= â€œin mtâ€

    {microtheory} ::= a string representing an instance of #$Microtheory



     {default-mt-directive} ::= {default-mt-keyword} â€œ:â€ {microtheory}

     {default-mt-keyword} ::= â€œdefault mtâ€

    {microtheory} ::= a string representing an instance of #$Microtheory



     {assertion-direction-directive} ::= {assertion-direction-keyword} â€œ:â€

    {assertion-direction-indicator}

     {assertion-direction-keyword} ::= â€œdâ€ | â€œalâ€ | â€œaccess levelâ€ | â€œdirectionâ€

    {assertion-direction-indicator} ::= â€œ:â€ {assertion-direction-indicator-keyword}

     | {assertion-direction-indicator-keyword}

     {assertion-direction-indicator-keyword} ::= â€œ0â€ | â€œforwardâ€

    | â€œ4â€ | â€œbackwardâ€

    | â€œcodeâ€ | â€œunknownâ€



    {assertion-truth-directive} ::= {assertion-truth-keyword} â€œ:â€

    {assertion-truth-indicator}

     {assertion-truth-keyword} ::= â€œtruth valueâ€ | â€œtvâ€

    {assertion-truth-indicator} ::= â€œ:â€ {assertion-truth-indicator-keyword}

     | {assertion-truth-indicator-keyword}

     {assertion-truth-indicator-keyword} ::= â€œ:defaultâ€ | â€œ:monotonicâ€ | â€œ:unknownâ€



    {constant-directive} ::= {constant-keyword} â€œ:â€ {constant-name}

     {constant-keyword} ::= â€œconstantâ€ | â€œunitâ€

    {constant-name} ::= a string representing the name of the constant



     {kill-directive} ::= {kill-keyword} â€œ:â€ {existing-constant}

     {kill-keyword} ::= â€œkillâ€

    {existing-constant} ::= a string representing an existing constant



     {rename-directive} ::= {rename-keyword} â€œ:â€ {existing-constant}

     {new-constant-name-string}

     {rename-keyword} ::= â€œrenameâ€

    {existing-constant} ::= a string representing an existing constant

     {new-constant-name-string} ::= a quoted string of the new constant name



     {include-ke-file-directive} ::= {include-ke-file-keyword} â€œ:â€ {filepath}

     {include-ke-file-keyword} ::= â€œincludeâ€

    {filepath} ::= path to the file



     {formula-directive} ::= {formula-keyword} â€œ:â€ {formula}

     {formula-keyword} ::= â€œfâ€ | â€œelâ€ | â€œformulaâ€

    {formula} ::= a CycL formula



     {predicate-assertion} ::= {pred-assertion-arity-2}

     | {pred-assertion-arity-3}

     | {pred-assertion-arity-4}

     | {pred-assertion-arity-5}

     {pred-assertion-arity-2} ::= {binary-pred} â€œ:â€ {atoms}

     {atoms} ::= {atom} | {atom} {atoms}

     {atom} ::= fort | string | number | ?TODO?

     {pred-assertion-arity-3} ::= {ternary-pred} â€œ:â€ {atom-pairs}

     {atom-pairs} ::= {atom-pair} | {atom-pair} {atom-pairs}

     {atom-pair} ::= â€œ(â€ {atom} {atom} â€œ)â€

    {pred-assertion-arity-4} ::= {quaternary-pred} â€œ:â€ {atom-triplets}

     {atom-triplets} ::= {atom-triplet} | {atom-triplet} {atom-triplets}

     {atom-triplet} ::= â€œ(â€ {atom} {atom} {atom} â€œ)â€

    {pred-assertion-arity-5} ::= {quintary-pred} â€œ:â€ {atom-quartets}

     {atom-quartets} ::= {atom-quartet} | {atom-quartet} {atom-quartets}

     {atom-quartet} ::= â€œ(â€ {atom} {atom} {atom} {atom} â€œ)â€

Appendix G ++++++++++

Common Cyc Abbreviations

Abbrev.

Definition

  
AIS

AbstractInformationStructure  

API Application Programmersâ€™ Interface Arg Logical â€˜argumentâ€™ position of some relation in the CYC KB. BLO \#$BiologicalLivingObject CNF Conjunctive Normal Form CW Conceptual Work CycL The Cyc description language; extended predicate logic; formerly called CL (Constraint Language), then EL (Epistemological Language); see \#$CycL (includes HL) DARPA Defense Advanced Research Projects Agency Defn Definition DNF Disjunctive Normal Form EL Epistemological Level (user-level representations) FI Functional Interface Fn Function FOPC First-Order Predicate Calculus fp Forward Propagate GAF Ground Atomic Formula genl Generalization (i.e. a more general term); \#$genls is star-closure GT General Transitivity HL Heuristic Level (an internal machine represention) HPKB The DARPA High-Performance Knowledge Bases project IBO \#$InformationBearingObject IBQS \#$IntervalBasedQuantitySlot IBT \#$InformationBearingThing IDE Integrated Development Environment IKB Integrated Knowledge Base â€” the version of the Cyc Knowledge Base released for the High-Performance Knowledge Base project KB \#$KnowledgeBase, specifically, the Cyc Knowledge Base KE Knowledge Entry (into the Cyc KB) KFD Knowledge Formation through Dialog LHS Left-Hand Side (of a rule); the antecedent MELD Moderately Expressive Logical Description language; a superset of CycL Mt \#$Microtheory MWW Multi-Word-Word NART Non-Atomic Reified Term NAT Non-Atomic Term; a function together with its argument(s) NAUT Non-Atomic Un-reified Term; a functional term that is semantically valid but Cyc has currently not thought about (like John Smithâ€™s great-great grandmother) NL Natural Language NLP Natural Language Processing; also Natural Language Parsing NLU Natural Language Understanding OE Ontological Engineer or Engineering (no longer used) PIT \#$PropositionalInformationThing pred \#$Predicate PSC \#$ProblemSolvingCntxt Reln Relation RHS Right-Hand Side (of a rule); the consequent RKF Rapid Knowledge Formation â€” the DARPA follow-on research project to HPKB SDBI Semantic Database Integration SKSI Semantic Knowledge Source Integration SME Subject Matter Expert spec Specialization (i.e. a more specialized term); (inverse of \#$genls); specs is star-closure STIB Short Time Interval Before \[see \#$STIB\] STIF Short Time Interval Following \[see \#$STIF\] SubL A dialect of Lisp designed to implement the Cyc application TMS Truth-Maintenance System WALES Web-Assisted Lexical Entry System WFF Well-formed formula; pronounced â€˜woof.â€™ Used as an adjective to denote correctness (i.e. â€˜This CycL sentence is not wff.â€™)

Appendix L ++++++++++

OpenCyc License

The OpenCyc Knowledge Base

The OpenCyc Knowledge Base consists of code, written in the declarative language CycL, that represents or supports the representation of facts and rules pertaining to consensus reality. OpenCyc is licensed using the Apache License, Version 2, whose text can be found here. The OpenCyc CycL code base is the â€œWorkâ€ referred to in the Apache license. The terms of this license equally apply to renamings and other logically equivalent reformulations of the Knowledge Base (or portions thereof) in any natural or formal language.

The OpenCyc Java API and Other Non-CycL Open Source Code

Some other programs from those listed above are provided as open source. All of the programs of this type that currently ship with OpenCyc use the Apache License, but it is possible that future released programs may use a different license. All license and copyright information for these programs are included in their distributions.

The OpenCyc Knowledge Server

The OpenCyc Knowledge Server consists of a binary derivative version of the CycÂ® Inference Engine and Knowledge Base Index, a binary derivative version of the CycÂ® Knowledge Base Browser, and a suite of tools for rapidly extracting knowledge from a domain expert.

Cycorp is providing a free-of-charge license to the OpenCyc Knowledge Server that grants the Licensee the irrevocable right to download, to use, and to distribute the OpenCyc Knowledge Server in binary form for commercial or non-commercial use. By obtaining information, software, and/or documentation of the OpenCyc Knowledge Server in whole or in part (collectively, â€œMaterialâ€), you agree to be legally bound by the following terms.

The OpenCyc OWL Ontologies

These files contain an OWL representation of information contained in the OpenCyc Knowledge Base. The content of these OWL files are licensed under the Creative Commons Attribution 3.0 license whose text can be found at <http://creativecommons.org/licenses/by/3.0/legalcode>. The content of these OWL files, including the OpenCyc content they represent, constitutes the â€œWorkâ€ referred to in the Creative Commons license. The terms of this license equally apply to, without limitation, renamings and other logically equivalent reformulations of the content of these OWL files (or portions thereof) in any natural or formal language, as well as to derivations of this content or inclusion of it in other ontologies.

Appendix SubL +++++++++++++

<http://www.cyc.com/documentation/subl-reference/>

I have been studying OpenCyc and I was disappointed when the SubL guide I found didn't have any mention of the KB creation and access commands.

I have also been using AIMLpad which is a Alice.org chatbot program. It had a Cyc interface. By inspecting the documentation that came with AMLpad.

{NOTE: I have been informed that the FI-\* commands are being depreciated, that CYC-\* commands should be used instead. I have not tested this and will update the page once I can provide concrete feedback)

SubL commands: (FI-CREATE '"Cone4" )

Creates a new constant in Cyc. (FI-ASSERT '(\#$isa \#$Cone4 \#$Cone) '\#$BaseKB ':Default 'nil)

Makes assertion into Cyc knowledgebase. The second argument is the name of the microtheory to assert the fact. The third argument is the chaining direction. (FI-UNASSERT '(\#$isa \#$TomBelpasso \#$Dog) '\#$BaseKB )

Retracts previously asserted facts. (FI-RENAME '\#$Cone4 "Cone6")

Changes the name of the constant to a new sting. (fi-ask '(\#$isa '?ISIT \#$Cone) \#$EverythingPSC)

Does a KB query.

These commands are queued, I think there are are versions of the commands that are immediately applied.

â€¢Introduction â€¢KE Text Syntax â€¢Appendix A: KE Text History â€¢Appendix B: KE Text Syntax

Appendix T ++++++++++ [KE-Text/Terms](KE-Text/Terms "wikilink")
