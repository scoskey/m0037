# MATH0037 Lecture Notes

By Samuel Coskey

Based partially upon texts and notes by H Enderton, S Thomas, K Kunen, and others.

<!--
Compiling
Comment out the toc
pandoc -H header.tex --shift-heading-level-by=-1 notes.md -o notes.pdf
-->

#### Table of contents

[Part I: Introduction to logic and set theory](#part-i-introduction-to-logic-and-set-theory)
- [1. Propositional logic](#1-propositional-logic)
- [2. Naive set theory and the proof of compactness](#2-naive-set-theory-and-the-proof-of-compactness)
- [3. Axiomatic set theory and foundations](#3-axiomatic-set-theory-and-foundations)

[Part II: First order logic and completeness](#part-ii-first-order-logic-and-completeness)
- [4. Syntax and theories](#4-syntax-and-theories)
- [5. Semantics, structures, and satisfaction](#5-semantics-structures-and-satisfaction)
- [6. Compactness and completeness](#6-completeness-and-compactness)
- [7. Applications of compactness, more about theories](#7-applications-of-compactness-more-about-theories)

[Part III: Computability theory and incompleteness](#part-iii-computability-theory-and-incompleteness)
- [8. Definability, absoluteness, and decidability](#8-definability-absoluteness-and-decidability)
- [9. Computable functions, recursion, and undecidable sets](#9-computable-functions-recursion-and-undecidable-sets)
- [10. Decidability in logic and incompleteness](#10-decidability-in-logic-and-incompleteness)

## Part I: Introduction to logic and set theory

#### Introduction

*Logic* is the area of study that concerns reasoning. It has of course been studied by both philosophers and mathematicians for several millennia.

In this module we will study *mathematical logic*, which has been studied since late 1800s. During that period mathematics itself was rapidly evolving and modernising, and mathematical logic was developed to help provide a rigorous foundation for contemporary mathematics.

Mathematical logic helps us understand what language we can use when discussing mathematics, what makes theorem statements meaningful, and what forms of reasoning are appropriate to use in proofs. It also helps us build and study mathematical structures like groups, rings, graphs, and so on.

The modern field of mathematical logic now consists of three interconnected subfields: first order logic, set theory, and computability theory.

In this module we will focus primarily on first order logic. However we will begin our study with the much simpler propositional logic, along with some elementary set theory to support our studies. We will conclude with an introduction to computability theory and the incompleteness phenomenon.

### 1. Propositional logic

We begin our study of mathematical logic with the relatively simple theory of *propositional logic*. This theory deals with the boolean connectives (P implies Q, and so forth) but excludes quantifiers (for all, there exists).

In the next part we will study first order logic, which adds the quantifiers back in. While that means the progress we make in this section will later be replaced, we include it to help us transition from basic logic to genuine mathematical logic.

We begin by introducing the *language* of propositional logic. Every language has an *alphabet*, or set of symbols we may write. The alphabet of propositional logic includes:

* the boolean connective symbols: $\neg$, $\wedge$, $\vee$, $\rightarrow$, $\leftrightarrow$
* propositional variable symbols: $P_1,P_2,P_3,\ldots$ (or sometimes $P,Q,R,\ldots$, $A,B,C,\ldots$, etc)
* brackets, also called parentheses: '$($', '$)$'

We will see later on that the connective symbols $\vee,\rightarrow,\leftrightarrow$ may all be avoided. Moreover, even the brackets may be avoided if one uses prefix notation instead of infix notation. (That is, if one writes $\mathord{\wedge}PQ$ instead of $(P\wedge Q)$.) For the moment we will continue with the more familiar infix notation.

Next, a language should tell us how to put symbols from the alphabet together.

**Definition** An *expression* is any finite sequence of symbols using the alphabet of propositional logic.

For example, both of the following are expressions:

* $(P\wedge Q)\vee R$
* $((P\rightarrow($

Clearly some expressions are more useful than others! The following definition helps us pick out the expressions which are more likely to have a useful meaning.

**Definition** An expression is called a *well-formed formula* (or *wff*, or simply *formula*) if it can be constructed using the following base case and recursive rule:

* Every propositional variable symbol is a formula
* If $\alpha$ and $\beta$ are formulas, then so are $(\neg\alpha)$, $(\alpha\wedge\beta)$, $(\alpha\vee\beta)$, $(\alpha\rightarrow\beta)$, $(\alpha\leftrightarrow\beta)$

For example, the following are all well-formed formulas:

* $((P\wedge Q)\vee R)$
* $(P\rightarrow ((\neg Q)\vee (R\rightarrow P)))$

The following are not well-formed formulas:

* $((P\rightarrow)$
* $P\wedge Q\mathbin{\neg} R$

The expression $(P\wedge Q)\vee R$ mentioned above technically **is not** a well-formed formula because it has too few brackets. As humans we can infer it intends to mean the same as $((P\wedge Q)\vee R)$. When there is no cause for confusion we will sometimes write such incorrect expressions, and ask the reader to mentally insert the needed brackets.

Many authors introduce an order of operations. For example if we state that $\wedge$ takes precedence over $\vee$ (which is standard for many authors), then $P\wedge Q\vee R$ may again be interpreted as $((P\wedge Q)\vee R)$. We will try to avoid this and include enough brackets to make it clear .

In logic we often separate the *syntax* and the *semantics* of formulas. Syntax is all about rules, you can think of it as analogous to grammar for languages. for example, what is and isn't considered a well-formed formula, much like grammar. On the other hand, semantics is all about meaning, for example, which formulas might be considered true or false.

The semantics of propositional logic is governed by truth tables. In the following, let $\alpha$ and $\beta$ be well-formed formulas.

$$\begin{array}{cc}\alpha&(\neg\alpha)\\\hline T&F\\F&T\end{array}$$

$$\begin{array}{ccc}\alpha&\beta&(\alpha\wedge\beta)\\\hline T&T&T\\T&F&F\\F&T&F\\F&F&F\end{array}$$

The boolean connective $\rightarrow$ always sparks a little bit of discussion.

$$\begin{array}{ccc}\alpha&\beta&(\alpha\rightarrow\beta)\\\hline T&T&T\\T&F&F\\F&T&T\\F&F&T\end{array}$$

This truth table attempts to capture the logic of "P implies Q", but it doesn't capture the causation we normally understand from natural language. It is sometimes called the *material conditional*. We can describe $\alpha\rightarrow\beta$ as a promise: if you know $\alpha$ is true then it promises $\beta$ is also true. Thus if $\alpha$ is not true, then no promise is made, and so the conditional is "vacuously true". We will see later that this definition is the most useful way to study deductions in mathematics.

We invite the reader to fill in truth tables for the rest of the boolean connectives.

While these truth tables are certainly familiar, we still need to describe how they are used. We will say the set of *truth values* is $\set{T,F}$.

**Definition** A *truth assignment* is a function $v$ from the set of propositional symbols to the set of truth values. That is, $v\colon\set{P_1,P_2,\ldots}\to\set{T,F}$.

In other words, a truth assignment $v$ says whether each propositional symbol is true or false. Since the propositional symbols are the simplest well-formed formulas, intuitively we should be able to use $v$ together with the truth tables for the boolean connectives to determine whether $v$ says any well-formed formula $\alpha$ is true or false. The following definition makes this idea formal.

**Definition** Let $v$ be a truth assignment and $\alpha$ be a well-formed formula. We define $v\models\alpha$, read aloud "$v$ satisfies $\alpha$", using the following base case and recursive rules:

* If $\alpha=P$ and $v(P)=T$, let $v\models\alpha$. If $v(P)=F$ let $v\not\models\alpha$.
* If $\alpha=\neg\beta$ and $v\models\beta$ then let $v\not\models\alpha$. If $v\not\models\beta$ then let $v\models\alpha$.
* If $\alpha=\beta\wedge\gamma$ and $v\models\beta$ and $v\models\gamma$ then let $v\models\alpha$; otherwise let $v\not\models\alpha$.
* We invite the reader to add an additional recursive rule for each boolean connective using truth tables described above.

For the record, we state that the above definition is *well-defined*, meaning that for any $v$ and $\alpha$ it follows from these rules that either $v\models\alpha$ or $v\not\models\alpha$, and not both. While this assertion may seem intuitively true or unnecessary, it should be proved, and we will postpone the proof until the next part.

When $v\models\alpha$ we think to ourselves that $\alpha$ is true under the assumptions contained within $v$. This is the semantic meaning of a well-formed formula $\alpha$: if we know the truth values of the propositional symbols then we can use the structure of $\alpha$ to derive the truth value of $\alpha$.

**Example** Let $\alpha$ be the well-formed formula $((P\leftrightarrow Q)\wedge(Q\rightarrow R))\rightarrow P$. In lecture we will consider several truth assignments $v$ and analyse in each case whether $v\models\alpha$.

Typically, different truth assignments will give rise to different truth values for $\alpha$. However for some very special formulas $\alpha$, the truth assignment may have no impact on the outcome. For instance, if $\alpha$ is the formula $P\vee\neg P$, then it is easy to check that every truth assignment $v$ results in $v\models\alpha$.

**Definition** A well-formed formula $\alpha$ is a *tautology* if for every truth assignment $v$ we have $v\models\alpha$.

The tautologies are thus little bits of reasoning that are always true, regardless of the truth values of the propositional variables. Another example of a tautology is $(P\wedge Q)\rightarrow P$. This is because any truth assignment that makes $P\wedge Q$ true must also make $P$ true.

**Definition** We say that $\alpha\models\beta$, read aloud "$\alpha$ semantically implies $\beta$", if for every truth assignment $v$, if $v\models\alpha$ then $v\models\beta$.

Semantic implication in propositional logic is sometimes also called "tautological implication". We invite the reader to verify that $\alpha\models\beta$ if and only if $\alpha\to\beta$ is a tautology.

**Example** Let $\alpha=(P\leftrightarrow Q)\wedge(Q\rightarrow R)$ and $\beta=P\rightarrow R$. In lecture we will run through the possibilities for $v$ and thereby conclude that $\alpha\models\beta$.

We next generalise the $\models$ notation once more to allow sets of formulas to be used.

**Definition** Let $v$ be a truth assignment and let $\Sigma$ be a set of well-formed formulas. We say $v\models\Sigma$, read "$v$ satisfies $\Sigma$", if for all $\sigma\in\Sigma$ we have $v\models\sigma$.

**Definition** Let $\Sigma$ be a set of well-formed formulas, and $\alpha$ be a well-formed formula. We say $\Sigma\models\alpha$ if for every truth assignment $v$, if $v\models\Sigma$ then $v\models\alpha$.

**Example** Let $\Sigma=\set{(\neg S)\vee R, R\rightarrow P, S}$, and let $\alpha=P$. In lecture we will show that $\Sigma\models\alpha$.

The semantic implication $\Sigma\models\alpha$ is more interesting when $\Sigma$ is infinite (why is this?). The next result states that even when $\Sigma$ is infinite, just a finite subset of $\Sigma$ is needed.

**Theorem** (Compactness theorem, version I). Let $\Sigma$ be a set of well-formed formulas. If $\Sigma\models\alpha$, then there exists a finite subset $\Sigma_0\subset\Sigma$ such that $\Sigma_0\models\alpha$.

The compactness theorem for propositional logic is one of the cornerstones of the theory, as will be the more general compactness theorem for first order logic. The name of the compactness theorem is due to its relationship to the idea of compactness in analysis, something which will become a little clearer later on.

The compactness theorem can be restated as a statement about consistency.

**Definition** Let $\Sigma$ be a set of well-formed formulas. We say $\Sigma$ is *consistent* if there exists a truth assignment $v$ such that $v\models\Sigma$.

We invite the reader to verify that $\Sigma$ is consistent if and only if $\Sigma\not\models (P\wedge(\neg P))$. Sometimes the symbol $\bot$ is used for a tautologically false formula such as $(P\wedge(\neg P))$. Thus we may say $\Sigma$ is consistent if and only if $\Sigma\not\models\bot$.

**Theorem** (Compactness theorem, version II). Let $\Sigma$ be a set of well-formed formulas. If every finite subset of $\Sigma$ is consistent, then $\Sigma$ is consistent.

We invite the reader to establish an equivalence between the two versions of the compactness theorem.

The compactness theorem has many interesting applications, to give a taste of this we explore just one of them from combinatorial graph theory. Recall that if $G=(V,E)$ is a graph with vertex set $V$ and edge set $E$, then a *proper coloring* of $G$ with $n$ colors is a function $\chi\colon V\to\set{c_1,\ldots,c_n}$ such that whenever $(v,v')\in E$ we have $\chi(v)\neq\chi(v')$.

**Corollary** Let $G$ be a combinatorial graph, finite or infinite. Suppose that every finite subgraph $G_0\subset G$ has a proper coloring with $n$ colors. Then $G$ has a proper coloring with $n$ colors.

*Proof*: They key is that proper colorability can be encoded using well-formed formulas. For convenience we will use the propositional variable symbols $P_{v,i}$, where $v$ ranges over the vertices $V$ and $i\in 1,\ldots,n$. We then let $\Sigma$ consist of the following axioms:

> * $P_{v,1}\vee\cdots\vee P_{v,n}$ for each $v\in V$ and each $i$
> * $\neg(P_{v,i}\wedge P_{v,j})$ for each $v\in V$ and each $i.j$ such that $i\neq j$
> * $\neg(P_{v,i}\wedge P_{w,i})$ for each $v,w\in V$ such that $(v,w)\in E$ and each $i$

The reader should verify that there exists a truth assignment $v$ that satisfies $\Sigma$ if and only if there exists a proper coloring $\chi$ with $n$ colors.

We claim $\Sigma$ is finitely satisfiable. To see this let $\Sigma_0\subset\Sigma$ be a finite subset. Note that since $\Sigma_0$ is finite and each sentence is finite in length, there exists a finite susbest $V_0\subset V$ of vertices appearing in the subscript of a propositional symbol in $\Sigma_0$. If we let $G_0$ be the subgraph of $G$ induced by $V_0$, then by hypothesis there exists a proper coloring $\chi_0$ of $G_0$ with $n$ colors. As observed in the previous paragraph, this implies that $\Sigma_0$ is consistent.

Therefore by the compactness theorem, $\Sigma$ is satisfiable. Again, as we have seen, this implies there exists a proper coloring of $G$ with $n$ colors. $\blacksquare$

This corollary itself has several important consequences. Recall that a bipartite graph is just another word for a graph with a proper coloring with $2$ colors. Thus if every finite subgraph of $G$ is bipartite, then $G$ is bipartite. Next recall the major theorem that every finite planar graph has a proper coloring with $4$ colors. Thus every planar graph (finite or infinite) has a proper coloring with $4$ colors.

#### Deductions

The concept of $\Sigma\models\alpha$ is a kind of implication, that is, we understand it to mean that if the formulas in $\Sigma$ are taken as true, then $\alpha$ is true. But the "proof" of $\alpha$ is tedious and unenlightening: go through every prossible truth assignment $v$, check whether $v$ satisfies each of the well-formed formulas in $\Sigma$, and if so, check whether $v$ satisfies $\alpha$.

How can we show that the truth of $\Sigma$ implies the truth of $\alpha$ using logical reasoning. The answer is a *deduction*, which is a sequence of steps, together with justification that each step follows from the previous ones. 

**Definition** Let $\alpha,\beta$ be well-formed formulas. *Modus ponens* is the deductive rule that if $\alpha$ is true, and $\alpha\rightarrow\beta$ is true, then $\beta$ is true.

We leave it to the reader to verify that the modus ponens rule is true semantically, that is, $\set{\alpha,\alpha\rightarrow\beta}\models\beta$. This should help shed some light on the reasons for the truth table for the connective $\rightarrow$.

**Definition** Let $\Sigma$ be a set of well-formed formulas, and let $\alpha$ be a well-formed formula. We define $\Sigma\vdash\alpha$, read "$\Sigma$ syntactically implies $\alpha$", if there exists a sequence of well-formed formulas $\alpha_1,\ldots,\alpha_n$ such that $\alpha_n=\alpha$, and for every $i\leq n$ at least one of the following is true:

> (a) $\alpha_i$ is a hypothesis, that is, an element of $\Sigma$  
(b) $\alpha_i$ is a tautology  
(c) $\alpha_i$ follows from two of the previous formulas in $\alpha_1,\ldots,\alpha_{i-1}$ by modus ponens

In other words, a deduction is a very simple kind of proof that the hypotheses $\Sigma$ imply the conclusion $\alpha$. While $\Sigma\models\alpha$ must be verified abstractly using truth tables, $\Sigma\vdash\alpha$ may be verified by checking the steps. The deduction includes its own reasoning.

We remark that it is overkill to allow *all* tautologies to be included in part (b) of the definition. Those who study deductions typically include only tautologies from a selected list of approved templates. For example, you can imagine including $\neg(\neg\alpha)\leftrightarrow\alpha$, $(\alpha\wedge\beta)\rightarrow\alpha$, and so on. By the same token, some authors use a minimal set of tautologies in (b) but expand the deductive rules allowed in (c). 

Since studying propositional logic is not our primary goal, we will stick with the simple definition (a)–(c) above in order to exposit a few key results. We invite the interested reader to to look up other standard deductive systems.

**Example** Let $\Sigma=\set{(\neg S)\vee R, R\rightarrow P, S}$ and let $\alpha=P$. We show that $\Sigma\vdash\alpha$ using the following deduction.

> 1. $(\neg S)\vee R$ — (hypothesis)
> 2. $((\neg S)\vee R)\rightarrow (S\rightarrow R)$ — (tautology)
> 3. $S\to R$ — (modus ponens)
> 4. $S$ — (hypothesis)
> 5. $R$ — (modus ponens)
> 6. $R\rightarrow P$ — (hypothesis)
> 7. $P$ — (modus ponens)

We have now introduced two distinct ways of understanding logical consequence, semantic implication $\Sigma\models\alpha$ and syntactic implication $\Sigma\vdash\alpha$. We should naturally try to understand how the two are connected, and in fact we will see that the two are equivalent. What's provable is true, and what's true is provable.

**Theorem** (Soundness and completeness theorems) Let $\Sigma$ be a set of well-formed formulas and $\alpha$ a well-formed formula. Then $\Sigma\models\alpha$ if and only if $\Sigma\vdash\alpha$. 

*Proof*: The soundness portion says that if $\Sigma\vdash\alpha$ then $\Sigma\models\alpha$, that is, deductions are valid or *sound*. This is due to the fact that every step in a deduction is valid. The steps of the form (a) and (b) are evidently valid, and the reader should have already checked that modus ponens (c) is valid. The result follows using induction along the length of the deduction.

The completeness portion says that if $\Sigma\models\alpha$ then $\Sigma\vdash\alpha$, that is, the deductions witness all the semantic implications and so are *complete*. To accomplish this, we first note that if $\Sigma\models\alpha$ then by the compactness theorem there exists a finite subset $\Sigma_0\subset\Sigma$ such that $\Sigma_0\models\alpha$.

Since $\Sigma_0$ is finite, we may enumerate now the well-formed formulas in $\Sigma_0$ as $\sigma_1,\ldots,\sigma_n$. We leave it to the reader to show there is a deduction from $\Sigma_0$ of the well-formed formula $\sigma_1\wedge\cdots\wedge\sigma_n$ (insert brackets appropriately). Furthermore, it follows from $\Sigma_0\models\alpha$ that $(\sigma_1\wedge\cdots\wedge\sigma_n)\rightarrow\alpha$ is a tautology. The last two claims plus modus ponens show that $\Sigma_0\vdash\alpha$, and therefore that $\Sigma\vdash\alpha$. $\blacksquare$

We see from the proof above that the compactness theorem implies the completeness theorem. We invite the reader to prove that the reverse is also true. The key is that $\vdash$ automatically satisfies the compactness-like property: if $\Sigma\vdash\alpha$, then there exists a finite subset $\Sigma_0\subset\Sigma$ such that $\Sigma_0\vdash\alpha$. This is true because any deduction of $\alpha$ from $\Sigma$ has finitely many steps, and therefore may only use finitely many of the well-formed formulas in $\Sigma$.

### 2. Naive set theory and the proof of compactness

In this section we take a short detour through set theory before returning to propositional logic and the compactness theorem. The primary reason is that some elementary set theory will be used in our further studies of logic. Moreover, set theory is very beautiful in its own right, and relevant to many areas of mathematics including analysis and algebra.

Beginning informally, a *set* is a collection of mathematical objects which we call *elements*. When $x$ is an element of the set $A$, we write $x\in A$. For instance $\mathbb Q$ is a set whose elements are the rational numbers, so for instance $\frac35\in\mathbb Q$ and $\sqrt2\notin\mathbb Q$.

For finite sets we may use the notation $x=\set{a_1,\ldots,a_n}$ to abbreviate that $x$ is a set and $a_1,\ldots,a_n$ are its only elements. We sometimes extend this to large sets and infinite sets using $\ldots$ notation, which means to continue a clear pattern. So for example $\mathbb N=\set{0,1,2,\ldots}$. We may also use the *set-builder* notation $A=\set{z:\text{some property of }z}$ to abbreviate that $A$ is the set of all elements $z$ that satisfy some property. For instance we may write $\mathbb N=\set{z:z\text{ is a natural number}}$.

The foundation of set theory is the *extensionality axiom*, which states that two sets are equal if and only if they have the same elements. Formally, if $A,B$ are sets then $A=B$ if and only if for all $x$, we have $x\in A\leftrightarrow x\in B$. This axiom distinguishes sets from other similar mathematical objects such as lists and multisets, by enforcing that the order of elements and the repetition of elements do not matter. For instance, if $A=\set{1,2,3}$ and $B=\set{3,2,2,1}$ then $A=B$.

You may be aware that this informal or "naive" approach is not entirely sound, as it can lead to falsehoods such as Russell's paradox. In this section no such paradoxes will arise, so we can proceed for now without worrying. In the next section, we will be more careful.

#### Pairs, relations, and functions

Here we introduce some foundational notation and constructs using sets. We assume the reader is already familiar with the meaning of the subset relation $\subset$ and the boolean operations $\cap$, $\cup$, and $\triangle$. We note that "complement" $\bar{A}$ is not an operation because we are not working with a universal set in which to take the complement. We may however use the set difference $B\smallsetminus A$, which means all elements of $B$ which are not in $A$.

**Definition** Given any two objects $a,b$, the *ordered pair* $(a,b)$ is defined to be the set $\set{\set{a},\set{a,b}}$.

We invite the reader to check that this construction "works" in the sense that two ordered pairs are equal if and only if their left and right components are equal. One should observe that many simpler attempts don't work, such as $\set{\lbrace a\rbrace,\lbrace b\rbrace}$ or $\set{a,\set{a,b}}$.

**Definition** Let $A,B$ be sets. The *cartesian product* of $A$ and $B$ is defined as $A\times B=\set{(a,b):a\in A,\ b\in B}$.

For instance, $\mathbb R\times\mathbb R$ is the Cartesian plane, and $\mathbb Z\times\mathbb Z$ is the grid points of the Cartesian plane.

**Definition** Let $A,B$ be sets.

* A *binary relation* between $A$ and $B$ is any subset $R\subset A\times B$. We sometimes write $aRb$ to mean that $(a,b)\in R$.
* The *domain* of $R$ is $\set{a\in A:(\exists b)(a,b)\in R}$
* The *range* of $R$ is $\set{b\in B:(\exists a)(a,b)\in R}$

For example, the $<$ relation on real numbers is a binary relation between $\mathbb R$ and itself. Formally, $<$ is the set of all pairs $(m,n)\in\mathbb R\times\mathbb R$ such that $m$ is less than $n$. Thus $<$ is "physically" a region in the plane.

Many important types of mathematical objects are binary relations. All of the following are binary relations: partial orders, linear orders, equivalence relations, combinatorial graphs, and so on. The $<$ example above is a linear order.

Another special example of a binary relation is a functions. In elementary mathematics, we often teach that a function is a formula or rule. But in formal mathematics, a function is "physically" its graph, which is the set of ordered pairs (input, output).

**Definition** Let $A$ and $B$ be sets.

* A *function* from $A$ to $B$ is a binary relation $f\subset A\times B$ with the property: for all $a\in A$ there exists a unique $b\in B$ such that $(a,b)\in f$.
* $f$ is *injective* or *one-to-one* if $(a,b),(a',b)\in f$ implies $a=a'$
* $f$ is *surjective onto* $B$ (or simply *surjective* when $B$ is clear from context) if the range of $f$ is equal to $B$.
* $f$ is *bijective* between $A$ and $B$ if it is injective and surjective onto $B$.

When $f$ is a function from $A$ to $B$ we may write $f\colon A\to B$, and when $(a,b)\in f$ we may write $f(a)=b$.

**Example** In lectures we will give some examples of functions, their graphs, and their properties.

**Definition** Let $A,B$ be sets. Then $B^A$ denotes the set of functions from $A$ to $B$.

We note that in other resources the set $B^A$ may be written as ${}^AB$ or $\mathrm{Fun}(A,B)$ (because it is fun).

When the exponent set is finite, we can think of $B^A$ as tuples of elements of $B$. In more detail, for each natural number $n$, let the symbol $n$ stand for the set $\set{0,\ldots,n-1}$. Then $B^n$ consists of all functions $f\colon\set{0,\ldots,n-1}\to B$. Given such a function $f$, we can think of it as an ordered $n$-tuple $(f(0),\ldots,f(n-1))$, which is a generalisation of an ordered pair.

**Definition** Let $X$ be a set. Then An $n$-ary *relation* on $X$ is a subset $R\subset X^n$.

For example, if $G$ is a group then it possesses a multiplication operation $g\cdot h$. We can think of $\cdot$ as a function $G\times G\to G$. We can also think of $\cdot$ as the ternary relation $R\subset G^3$ consisting of all triples $(g,h,j)\in R$ such that $g\cdot h=j$.

#### Rooted trees, Konig's lemma, and compactness

In combinatorics a tree is a special kind of combinatorial graph, one without cycles. In set theory we view trees slightly differently, with a root vertex and other vertices labeled by elements of a set $X$. Here we introduce the set-theoretic terminology and notation surrounding trees.

**Defintion**. Let $X$ be any set.

* The *full tree* on $X$, denoted $X^{<\mathbb N}$, is defined as $\bigcup_{n\in\mathbb N}X^n$.
* The $n$-th *level* of $X^{<\mathbb N}$ is $X^n$; we say elements on this level have *length* $n$.
* If $s,t\in X^{<\mathbb N}$, we say $s$ is a *predecessor* of $t$, or $t$ is a *successor* of $s$, if $s\subset t$.
* $t$ is an *immediate successor* of $s$ if $t$ is a successor of $s$ and $\vert t\vert=\vert s\vert+1$.

**Definition** Let $X$ be any set. A *tree* on $X$ is a subset $T\subset X^{<\mathbb N}$ of the full tree on $X$ which is closed under predecessors, that is, for all $s,t\in X^{<\mathbb N}$, if $s\subset t\in T$ then $s\in T$.

In lectures we will give several examples of set-theoretic trees.

**Definition** Let $X$ be any set.

* The set of sequences on $X$, denoted $X^{\mathbb N}$ is the set of all functions $f\colon\mathbb N\to X$.
* For any sequence $f\in X^{\mathbb N}$ and any $n\in\mathbb N$ the *restriction* of $f$ to $n$, denoted $f\restriction n$, is the initial segment of $f$ with domain $\set{0,\ldots,n-1}$.
* Let $T$ be a tree on $X$. A sequence $f\in X^{\mathbb N}$ is a *branch* through $T$ if for all $n\in\mathbb N$ we have $f\restriction n\in T$.

In lectures we will give several examples of branches through set-theoretic trees.

We now give a fundamental application of the propositional compactness theorem to the study of trees and branches.

**Theorem** (Konig's lemma) Let $T$ be a tree on $X$ such that every level of $T$ is nonempty and finite. Then there exists a branch through $T$.

We invite the reader to give an example of a tree $T$ such that every level of $T$ is nonempty but there are no branches through $T$.

*Proof*: They key is that the existence of a branch can be encoded using well-formed formulas. For convenience we will use the propositional variable symbols $P_t$, where $t$ ranges over the elements of $T$. We then let $\Sigma$ consist of the following axioms:

> * $P_{t_1}\vee\cdots\vee P_{t_k}$ where $t_1,\ldots,t_k$ is the list of elements of $T$ of length $n$, for each $n$
> * $\neg(P_{t_i}\wedge P_{t_j})$ where $t_1,\ldots,t_k$ is the list of elements of $T$ of length $n$, for each $n$ and each $i\neq j$
> * $P_t\rightarrow P_s$ where $s,t\in T$ and $s\subset t$

The reader should verify that there exists a truth assignment $v$ that satisfies $\Sigma$ if and only if there exists a branch through $T$.

We claim $\Sigma$ is finitely satisfiable. Let $\Sigma_0\subset\Sigma$ be a finite subset, and note that there exists a maximum level $n\in\mathbb N$ which is the length of an element appearing in the subscript of a propositional symbol in $\Sigma_0$. Since $T$ is infinite, $T$ certainly contains a partial branch up to level $n$, and this implies that $\Sigma_0$ is consistent.

Therefore by the compactness theorem, $\Sigma$ is consistent. This implies there exists a branch through $T$. $\blacksquare$

Konig's lemma has many important applications, we present just one. We first recall that the set $X^{\mathbb N}$ is a metric space, where two sequences are close together if they agree on a long partial sequence. Formally we let $d(f,g)=1/N$, where $N$ is the maximum number such that $f\restriction N=g\restriction N$. Thus a sequence of elements $f_n\in X^{\mathbb N}$ converges to $f\in X^{\mathbb N}$ if the length of agreement between $f_n$ and $f$ goes to infinity.

**Theorem** Let $2=\set{0,1}$. The metric space $2^{\mathbb N}$ is compact.

*Proof*: Let $f_n\in 2^{\mathbb N}$. We wish to show that there exists a subsequence of $f_n$ which converges to some limit $f\in 2^{\mathbb N}$ in the sense of the metric described above.

Let $T$ be the set of all $s\in 2^{<\mathbb N}$ such that $s\subset f_n$ for infinitely many $n\in\mathbb N$. Then it is easy to verify that $T$ is a tree. Moreover, the pigeonhole principle implies that the levels of $T$ are nonempty. Thirdly, since $T\subset 2^{<\mathbb N}$, the levels of $T$ are obviously finite. Therefore by Konig's lemma there exists a branch $f$ through $T$.

We now construct a subsequence of $f_n$ which converges to $f$. To do so, first observe that for every $k$ there are infinitely many $n\in\mathbb N$ such that $d(f,f_n)\leq1/k$. We can therefore inductively choose indices $n_k$ such that: (1) $d(f,f_{n_k})\leq1/k$, and (2) $n_k>n_{k-1}$. We have therefore found a subsequence $f_{n_k}$ of $f_n$ which converges to $f$. $\blacksquare$

We are now ready to return from our detour into set theory (and some light analysis) to the propositional compactness theorem. 

Recall that a truth assignment is a function $v\colon\set{P_1,P_2,\ldots}\to\set{T,F}$. We observe that if we identify $P_1,P_2,\ldots$ with natural numbers $1,2,\ldots$, and identify $\set{T,F}$ with $\set{0,1}$, then the set of truth assignments $v$ is equivalent to the set $2^{\mathbb N}$. In what follows we will use this equivalence freely, and in particular we will use the same metric of agreement that we used in the previous result.

We invite the reader to verify that if $\alpha$ is any well-formed formula, then the set $V_\alpha$ of all truth assignments $v$ such that $v\models\alpha$ is a closed subset of $2^{\mathbb N}$. By the same argument, if $A$ is any finite set of well-formed formulas, then the set $V_A$ of all truth assignments $v$ such that $v\models A$ is a closed subset of $2^{\mathbb N}$ also.

**Theorem** (Compactness theorem) Let $\Sigma$ be a set of well-formed formulas such that every finite subset of $\Sigma$ is consistent. Then $\Sigma$ is consistent.

*Proof*: We recall the following fact from analysis. Let $X$ be a compact metric space, and let $\mathcal F$ be a family of closed subsets of $X$. If for all $A_1,\ldots A_n\in\mathcal F$ we have $A_1\cap\cdots\cap A_n\neq\emptyset$, then $\bigcap\mathcal F\neq\emptyset$. (In fact this may be taken as the definition of a compact metric space.)

Working in the space $2^{\mathbb N}$, we let $\mathcal F$ be the family of all $V_A$ where $A$ is a finite subset of $\Sigma$. Observe that if $V_{A_1},\ldots, V_{A_n}\in\mathcal F$ then $V_{A_1}\cap\cdots\cap V_{A_n}=V_{A_1\cup\cdots\cup A_n}$. Since $A_1\cup\cdots\cup A_n$ is a finite subset of $\Sigma$, it is consistent, and therefore there exists $v$ such that $v\models A_1\cup\cdots\cup A_n$. By definition this implies $v\in V_{A_1}\cap\cdots\cap V_{A_n}$, so $V_{A_1}\cap\cdots\cap V_{A_n}\neq\emptyset$.

It follows from the fact from analysis that there exists $v\in\bigcap_{V_A\in\mathcal F}V_A$. Again by definition this means that $v\models\Sigma$. Thus, $\Sigma$ is consistent. $\blacksquare$

We remark that the results of this section show that the following three statements are all equivalent:

> * The compactness theorem
> * Konig's lemma
> * The space $2^{\mathbb N}$ is compact

This gives some some explanation of the reason for the name of the compactness theorem. Of course, it is also possible to prove each of the three of these results directly. We invite the reader to find such proofs in our references or else look for them yourself.

We should acknowledge that we have only proved the compactness theorem when there is a *countable* set of propositional variable symbols $P_1,P_2,\ldots$. The compactness theorem remains true when there is an uncountable set of propositional variable symbols. This statement is stronger, and some of the steps of the proof will be different.

### 3. Axiomatic set theory and foundations

We have said informally that a set is a collection of mathematical objects which are its elements. But what is a set and what is an element, really? In this section we introduce *axiomatic set theory*, which tells us more formally where sets come from, what constructions are permitted, and thus helps us better understand what sets really are.

We then go on to show that set theory is in some sense a "theory of everything", meaning nearly all mathematical objects can be defined using sets. We have already seen this to some extent, for instance we showed that relations and functions may actually be defined as special kinds of sets. We can additionally construct mathematical objects of central importance such as number systems, metric spaces, measure spaces and so forth. The possibilities are endless, and by the end you will be able to imagine how to extend these constructions much further.

Lastly set theory is the key to studying the infinite. We will conclude the section with a brief introduction to ordinals.

#### Axiomatic set theory

The starting point for axiomatic set theory is the following big idea: **everything** is a set! We have so far seen many examples of sets of sets, that is, sets whose elements are sets themselves. Are there any other types of elements, are there any objects that aren't themselves sets? To a pure set theorist, everything is a set.

What is needed is therefore not a *definition* of set (everything is a set), but rather *axioms* of sets, which govern how sets behave and how we can construct them. Historically it took some time and debate for mathematicians to agree on axioms. Here we elaborate the axioms of *Zermelo–Fraenkel–Choice* set theory or ZFC, which is the officially accepted list.

We have already introduced the key axiom of ZFC, which explains the relationship between $\in$ and $=$.

**Axiom** (Extensionality) $x=y$ iff for all $z$, $z\in x\iff z\in y$.

The next several axioms of set theory are construction axioms, that is, axioms that tell us we can do certain operations or constructions using sets.

**Axiom** (Strong Pairing) If $a_1,\ldots,a_n$ are sets, then $\set{a_1,\ldots,a_n}$ is a set.

For one thing, the Strong Pairing axiom implies that there exists a set. Namely, if we apply it in the case when $n=0$ then the result is $\lbrace\rbrace$, which we also call the empty set $\emptyset$. We invite the reader to verify that the Strong Pairing axiom implies that ordered pairs may be constructed.

We say that a set is *hereditarily finite* if it may be constructed using only repeated applications of the Strong Pairing axiom. We invite the reader to write out several dozen hereditarily finite sets, and to make a diagram of these sets as they are related by the $\in$ relation. (That is, when $x\in y$ draw an upwards arrow from $x$ to $y$.)

Without any other axioms, the Strong Pairing axiom can *only* help us construct hereditarily finite sets. In addition to being the theory of everything, set theory is meant to be the theory of infinity! Therefore we need the following axiom, which lets us construct our first example of an infinite set.

**Axiom** (Infinity) There exists a set HF such that $x\in HF$ if and only if $x$ is hereditarily finite ($x$ can be constructed using only the Strong Pairing axiom).

Putting the last two axioms together, we may also construct an first example of a finite but not hereditarily finite set, namely, $\lbrace HF\rbrace$. However, the axioms so far do not help us construct an infinite set besides HF.

In order to construct new sets, we would like an axiom which allows us to define sets using properties. In the previous section we introduced the informal set-builder notation $\set{x:\text{some property of }x}$. However it turns out this is *too* informal!

Indeed we cannot construct a set of the form $A=\set{x:x\notin x}$. If you haven't done it before, we invite you to check that the definition of $A$ implies both $A\in A$ and $A\notin A$ are false, which is a contradiction. This is known as *Russell's paradox*, and as we define our axioms we must navigate around this issue.

While we can't expect to use general set-builder constructions, the following axiom states we can use *bounded* set-builder constructions, meaning set-builder constructions taking place inside a given set.

**Axiom** (Separation) If $A$ is a set and $P(x)$ is a property of sets $x$, then the set $\set{x\in A:P(x)\text{ is true}}$ exists.

The axiom is also sometimes called Specification or (restricted) Comprehension. In the next part, we will elaborate further on the exact nature of the properties $P(x)$ which may be used. For now, we will continue to be *somewhat* informal and use standard mathematical language to express these properties.

For instance we could let $E=\set{x\in HF:x\text{ has an even number of elements}}$. Then $E$ is a new infinite set which is a subset of HF.

The Separation axiom allows us to construct sets which are contained in a set we have already. What about constructing sets which are larger? One way to do this is the following.

**Axiom** (Power Set) If $A$ is a set then there exists a set $\mathcal P(A)$ called the *power set* of $x$ which consists of all subsets of $A$.

We invite the reader to verify that the Power Set axiom, together with the other axioms thus far, may also be used for other constructions such as $A\times B$ and $B^A$.

One familiar operation on sets that we haven't mentioned so far is the union $A\cup B$. Although they are powerful, surprisingly, the axioms we have listed so far do not allow us to construct unions.

**Axiom** (Union) If $\mathcal F$ is a set, then there exists a set $\bigcup\mathcal F$ called the *union* of $\mathcal F$, which consists of all $x$ such that $x\in F$ for some $F\in\mathcal F$.

In particular, if $A,B$ are sets we can construct $A\cup B$ by first using Pairing to construct $\set{A,B}$, and then using Union to construct $\bigcup\set{A,B}$, which is simply another way of writing $A\cup B$.

Of course we have introduced several operations on sets besides unions, including intersections $\cap$, set difference $\smallsetminus$, and symmetric difference $\triangle$. We invite the reader to verify that these constructions may be carried out using the axioms we have introduced, and do not require separate axioms.

There is one more construction axiom called the *Replacement* axiom, which we will not cover here. This axiom allows the construction of orderings of very long length and sets of very large cardinality.

There are several more axioms which are not explicit constructions like those above, but which instead help define the structure of the sets. The first of these is the *Choice* axiom or *AC*, which states that if $\mathcal F$ is a set of nonempty, pairwise disjoint sets, then there exists a set $C$ which contains exactly one element from each $F\in\mathcal F$.

AC is famously equivalent to a list of other nonconstructive statements which are widely used throughout mathematics: Zorn's lemma, every set can be well-ordered, every equivalence relation has a system of representatives, every vector space has a basis, and more. We will not cover these equivalences here, but we will use AC when necessary.

The last axiom is the *Regularity* axiom, which states that there does not exist an infinitely descending $\in$-sequence. That is, there does not exist a sequence of sets $x_1,x_2,x_3,\ldots$ such that $x_{n+1}\in x_n$ for all $n$. This axiom ensures, among other things, that circular relationships such as $x\in x$ or $x\in y\in x$ are never true.

#### Foundations

We now proceed to use the axioms to show how many familiar objects in mathematics may in fact be encoded as sets.

Perhaps the simplest and most important objects are the natural numbers $0,1,2,\ldots$ or sometimes $1,2,\ldots$. Previously we have used the natural numbers informally, such as when we introduced the propositional variable symbols $P_1,P_2,\ldots$, or when we stated the Pairing axiom starting from given sets $a_1,\ldots,a_n$. But how are natural numbers defined?

The first answer is that we will actually *continue* to allow ourselves to use them informally and without definition. This is part of what's called *metatheory*, or a basis of reasoning so primitive that we never formalise it. Metatheory also includes concepts like "symbol" and "finite sequence of symbols", and is necessary to prevent an unending series of questions of the form, "And how is *that* defined?".

The second answer is that we will also construct the natural numbers using set theory. Thus the informal natural numbers in the metatheory will have formal analogs in set theory. This is necessary to allow us to progress forwards and construct the *set* of natural numbers, something not present in the metatheory.

The *von Neumann* natural numbers are constructed as follows:

* $0=\emptyset=\lbrace\rbrace$
* $1=\lbrace0\rbrace=\lbrace\lbrace\rbrace\rbrace$
* $2=\lbrace0,1\rbrace=\lbrace\lbrace\rbrace,\lbrace\lbrace\rbrace\rbrace\rbrace$
* $3=\lbrace0,1,2\rbrace=\lbrace\lbrace\rbrace,\lbrace\lbrace\rbrace\rbrace,\lbrace\lbrace\rbrace,\lbrace\lbrace\rbrace\rbrace\rbrace\rbrace$
* $\vdots$

In general, we recursively define:

* $n+1=n\cup\lbrace n\rbrace$

We have already used this idea when we introduced $X^n$. At that time we said that we were using $n$ as a symbol representing the set $\set{0,\ldots,n-1}$. We now see that this was not an abuse of notation nor a convenience, it is actually von Neumann's true definition!

From the above definition we see that natural numbers are all elements of HF. Thus we can use the Separation axiom to construct the set of natural numbers.

**Definition** $\mathbb N=\set{x\in HF:x\text{ is a von Neumann natural number}}$.

We remark that because the definition of von Neumann natural number is recursive, some work is required to show that it is valid to use the property "$x$ is a von Neumann natural number" in the Separation axiom. We refer the interested reader to the *principle of recursive definitions*, which follows from the axioms.

In order to complete the construction of $\mathbb N$, it is also necessary to define the functions $+$ and $\times$. We may think of these as ternary relations, so for instance $+$ is really the set of all ordered triples $(m,n,s)\in\mathbb N^3$ such that $m+n=s$. The definition of $+$ is again recursive: if $(m,n,s)\in+$ then $(m+1,n,s+1)\in +$ and $(m,n+1,s+1)\in +$. Once again the principle of recursion tells us $+$ exists.

Now that we have achieved the construction of $\mathbb N$ in set theory, it is possible to construct further number systems.

**Definition** $\mathbb Q$ is the set of ordered triples $(i,m,n)$ in $2\times\mathbb N\times\mathbb N$ satisfying $n\neq0$ and $\mathrm{gcd}(m,n)=1$.

Of course, we think of $(0,m,n)$ as representing $\frac mn$ and $(1,m,n)$ as representing $-\frac mn$. (Or vice versa if you like.) Using several cases, it is an exercise to define $+$, $\times$, and $<$ on $\mathbb Q$. For instance $(0,m,n)\times(0,m',n')=$ the result of canceling common factors from $(0,mm',nn')$.

**Definition** $\mathbb Z$ is the set of all $(i,m,n)\in\mathbb Q$ satisfying $n=1$.

With these definitions, $\mathbb Z\subset\mathbb Q$ as one would expect, but unfortunately it is not technically the case that $\mathbb N\subset\mathbb Z$. We invite the reader to write a bijection from $\mathbb N$ to a subset of $\mathbb Z$, showing that we can think of $\mathbb N$ as a subset of $\mathbb Z$ if we wish.

So far, all the numbers we have constructed are elements of HF and the number systems are elements of $\mathcal P(HF)$. We are now ready to construct real numbers. Each real number will be a subset of HF, so the set of real numbers itself is an element of $\mathcal P(\mathcal P(HF))$.

**Definition** $\mathbb R$ is the set of *Dedekind cuts* of $\mathbb Q$. Here $C\subset\mathbb Q$ is a Dedekind cut if:
> * $C\neq\emptyset$, $\mathbb Q$
> * $C$ is closed downwards
> * $C$ has no last element

Once again $\mathbb Q$ is not officially a subset of $\mathbb R$, but using a bijection we can identify $\mathbb Q$ with a subset of $\mathbb R$. We may also use our definition of $+,\times,<$ on $\mathbb Q$ to define $+,\times,<$ on $\mathbb R$. For instance, we can define $C+C'=\set{q+q':q\in C,q'\in C'}$.

Having defined the real numbers, we can now continue to define nearly all familiar objects in mathematics.

**Definition**

* $\mathbb C$ is the set $\mathbb R\times\mathbb R$. Each ordered pair $(x,y)$ is interpreted as the complex number $x+iy$.
* $\mathbb R[x]$ is the set $\mathbb R^{<\mathbb N}$. Each sequence $a_0,\ldots,a_n$ is interpreted as the polynomial $a_0+a_1x+\cdots+a_nx^n$.
* $\mathbb R[[x]]$ is the set $\mathbb R^{\mathbb N}$. Each sequence $a_0,a_1,\ldots$ is interpreted as the formal power series $\sum a_nx^n$.
* $C(\mathbb R)$ is the subset of $\mathbb R^{\mathbb R}$ consisting of the functions which are continuous (use the $\epsilon,\delta$ definition!)
* $D(\mathbb R)$ is the subset of $\mathbb R^{\mathbb R}$ consisting of the functions which are differentiable (use the limit definition!)

While it may appear that the definitions we have given are universal or absolute, in truth there are a wide variety of different approaches to carrying out these constructions. For instance it's possible to construct $\mathbb R$ using Cauchy sequences, or to construct $\mathbb C$ as the algebraic closure of $\mathbb R$. The key is to check that the construction satisfies the desired properties, and that any two such constructions are isomorphic.

Another area that can be formalised in set theory is logic itself. Indeed, we have said that mathematical logic is just another area of mathematics, so for set theory to be an appropriate foundation it should include logic too. Once again there is an initial portion of logic which can be carried out using the metatheory, but it will also be mirrored in the formal theory.

We begin by encoding the alphabet of propositional logic $P_1,P_2,\ldots$ and $\neg,\wedge,\vee,\rightarrow,\leftrightarrow$ as natural numbers. For example we can use even numbers $0,2,4,$ to represent propositional variable symbols $P_1,x_2,\ldots$, and odd numbers $1,3,5,7,9$ for the logical connectives. Next, we encode an expression as a finite sequence of natural numbers, or element of $\mathbb N^{<\mathbb N}$. The well-formed formulas correspond to a subset of $\mathbb N^{<\mathbb N}$ arising from our recursive definition. Finally, we encode a proof using a sequence of logical expressions, and thus an element of $(\mathbb N^{<\mathbb N})^{<\mathbb N}$. Thus even a proof is an element of HF!

#### Infinity

We close this section with a discussion of the infinite. Set theory is not only appropriate as a foundation of "real-world" mathematics like calculus and analysis. It is also appropriate as a foundation for the study of the infinite. The key is that the axiom of infinity not only opens the door to infinite sets like $\mathbb Q$ and $\mathbb R$, but also to infinite sets of much larger cardinality.

The starting observation is that we can extend the von Neumann natural numbers into transfinite counting numbers. Recalling that every von Neumann natural number is equal to the collection of numbers that came before it, we can continue the pattern by setting $\omega=\set{0,1,2,3,\ldots}$ (infinity?) and continuing with $\omega+1=\set{0,1,2,3,\ldots,\omega}$ (infinity plus one?). The resulting objects are called the *ordinal numbers*:

* $0$
* $1$
* $\vdots$
* $n$
* $\omega=\bigcup_{n\in\mathbb N}n$
* $\omega+1=\omega\bigcup\lbrace\omega\rbrace$
* $\omega+2=(\omega+1)\cup\lbrace\omega+1\rbrace$
* $\vdots$
* $\omega+\omega=\bigcup_{n\in\mathbb N}(\omega+n)$
* $\omega+\omega+1=(\omega+\omega)\cup\lbrace\omega+\omega\rbrace$
* $\vdots$

Each ordinal in the sequence falls into one of two types. The *successor* ordinals are those $\alpha$ of the form $\beta\cup\lbrace\beta\rbrace$ for some ordinal $\beta$. We sometimes use the notation $S(\beta)$ or $\beta+1$ for the set $\beta\cup\lbrace\beta\rbrace$ because it is the successor of $\beta$. The *limit* ordinals are those $\lambda$ which are not the successor of any ordinal, such as $\omega$ and $\omega+\omega$. Instead a limit ordinal $\lambda$ is the union of all ordinals that came before, that is, $\lambda=\bigcup\set{\beta:\beta<\lambda}$.

(This last equation is a fact and not a definition or construction. It isn't suitable as a definition because it is circular with $\lambda$ on both sides. To construct ordinals properly, somewhat more work is needed: an ordinal is a transitive set whose elements are linearly ordered by the $\in$ relation.)

With ordinals it is possible to count as far into the transfinite as we can imagine. It follows from the axioms (AC is necessary here) that every set $A$ can be enumerated using some ordinal $\alpha$ as the set of indices. That is, it is possible to write $A=\set{a_\beta:\beta<\alpha}$. When the set $A$ is countable, the ordinal $\alpha$ can simply be taken to be $\omega$. When $A$ is uncountable, a larger ordinal is needed. So for instance even though $\mathbb R$ is uncountable, there exists an ordinal $\alpha$ such that $\mathbb R=\set{r_\beta:\beta\in\alpha}$. The same is true of $\mathcal P(\mathbb R)$, though of course it requires an even larger ordinal!

## Part II: First order logic and completeness

#### Introduction

The propositional logic we studied in the first part is a mathematical language that captures some portion of the reasoning that we do as mathematicians. It captures the conditional $\rightarrow$ particularly well, and helped us with meaningful applications including graph coloring and Konig's lemma.

However the propositional language with its boolean connectives still leaves much of mathematical reasoning out. For example it is impossible to imagine codifying real analysis or set theory using propositional logic alone. For example the definition of limit begins "for all $\epsilon$...". Similarly the axiom of Infinity begins "there exists a set HF such that...". The key concepts that we still need are the *quantifiers* "for all" and "there exists".

In this part we introduce and elaborate on first order logic, which is logic with boolean connectives and quantifiers. The term "first order" means the quantifiers range over elements of a given universe. We will not study "second order" logic, but in case you're curious it means the quantifiers may range over sets and functions as well.

We will see that first order logic is powerful enough to express nearly all mathematical concepts. But it strikes a balance, because it is also simple enough that we can reason and prove thoerems about it.

### 4. Syntax and theories

In the first part of the first section we introduced syntax suitable for propositional logic. In this section we will expand the syntax for first order logic. This time there are more kinds of symbols, so we will begin with a very general approach. Rather than working with a fixed alphabet (boolean connectives, propositional logic), we simply define that an *alphabet* $A$ is any set of symbols.

**Definition** An *expression* in the alphabet $A$ is a finite sequence of symbols of $A$.

Our intension is to let the alphabet include logical symbols as before, in addition to operation symbols (relations or functions) such as $+$, $\times$, and $<$.

In mathematics there are several notations for expressing an operation with one or more inputs. In *prefix* notation, the operation goes first, for instance $\neg P$, $f(x)$, $-3$. In *infix* notation, the operation goes in the middle, for instance $P\rightarrow Q$, $x+y$, $x>y$. In *postfix* notation the operation goes at the end, for instance $n!$, $f'$, $x^\ast$. (There are more concepts such at $\bar x$, but let's leave it at that.)

To avoid difficulties caused by parentheses, we officially adopt prefix notation for everything. For instance we can write $P\rightarrow (Q\rightarrow R)$ without parentheses as $\mathord{\rightarrow}P\mathord{\rightarrow}QR$. And we can write $(P\rightarrow Q)\rightarrow R$ without parentheses as $\mathord{\rightarrow}\mathord{\rightarrow}PQR$. It also eliminates the need for parentheses.

It will be the same way with operations as well as logical symbols like $\rightarrow$. For example the expression $n!+n>5$ will be written $>+!nn5$. It is worth spending a minute think about this!

While prefix expressions are our official standard, we will often write infix expressions with the understanding that the reader may imagine them converted to prefix appropriately.

In order to interpret prefix expressions, a person would need to know that the $!$ operation takes just one input, while $>$ and $+$ each take two inputs. The number of inputs for a given symbol is called its *arity*. The next definition incorporates arity into our language.

**Definition** A *lexicon* consists of an alphabet $A$ together with an arity function $a\colon A\to\mathbb N$.

For example, a lexicon for expressing polynomials with coefficients $1$–$4$ consists of alphabet $\set{1,2,3,4,x,+,\cdot}$ with arity function $a(1),\ldots,a(4),a(x)=0$ and $a(+)=a(\cdot)=2$. Then the expression $\mathord{+}\mathord{\cdot}3\mathord{\cdot}xx\mathord{+}\mathord{\cdot}2x1$ is one way to represent the polynomial $3x^2+2x+1$. (There are several other equivalent representations due to associativity and commutativity.)

**Definition** An expression is *well-formed* if it is of the form $s\tau_1\cdots\tau_n$ where $a(s)=n$ and $\tau_1,\ldots,\tau_n$ are well-formed expressions.

**Example** In lectures we will give examples of will-formed and non well-formed expressions. One example is the expression above, which begins with $s=\mathord{+}$ and is followed by $\tau_1=\mathord{\cdot}3\mathord{\cdot}xx$ and $\tau_2=\mathord{+}\mathord{\cdot}2x1$. Each of these may then be further broken down in a tree-like fashion. The expression $\mathord{+}\mathord{\cdot}xx$ is not well-formed.

Considering the example $\mathord{+}\mathord{\cdot}3\mathord{\cdot}xx\mathord{+}\mathord{\cdot}2x1$, it is natural to ask, can this string of symbols be read in two different ways? We know the first $+$ symbol should be followed by two arguments, but is there only one way to break the rest of the expression up into two arguments? This is a subtle but important question, and the next theorem tells us the answer is Yes.

**Theorem** (Unique readability) Let $\alpha$ be a well-formed expression.

1. No proper initial segment of $\alpha$ is well-formed.
2. If $\alpha$ starts with the symbol $s$, and $s$ is of arity $n$, then there exist unique well-formed expressions $\tau_1,\ldots,\tau_n$ such that $\alpha=s\tau_1\cdots\tau_n$.

*Proof*: Assume (1) and (2) are true for all expressions which are shorter than $\alpha$. By definition of well-formed, there exist well-formed $\tau_i$ such that $\alpha=s\tau_1\cdots\tau_n$. Let $\alpha'$ be a well-formed initial segment of $\alpha$ (not necessarily proper), and let $\tau'_1,\ldots\tau'_n$ be well-formed such that $\alpha'=s\tau'_1\cdots\tau'_n$. Then $\tau_1=\tau'_1$ since otherwise one would be an initial segment of the other, contradicting the inductive hypothesis. Similarly we can argue $\tau_i=\tau'_i$ for all $i$. Thus $\alpha'=\alpha$ and the $\tau_i$ are unique, establishing both (1) and (2). $\blacksquare$

**Corollary** If $\alpha$ is well-formed, then every symbol of $\alpha$ is the beginning of a unique well-formed subexpression. We call this subexpression the *scope* of the occurrence of the symbol.

*Proof*: Assume the theorem is true for expressions shorter than $\alpha$. By the previous theorem, the first symbol of $\alpha$ has scope $\alpha$. Any other symbol of $\alpha$ appears in some $\tau_i$. Since $\tau_i$ is shorter than $\alpha$, we can apply the inductive hypothesis. $\blacksquare$

In lectures, we will give examples of the scope of several symbols in an expression.

#### First order syntax

We now apply our knowledge of syntax to first order logic. The *basic lexicon* of first order logic consists of the alphabet $A=\set{\neg,\wedge,\vee,\rightarrow,\leftrightarrow,\forall,\exists,=}\cup\set{x_n:n\in\omega}$. The arity of the symbols are defined by $a(x_i)=0$, $a(\neg)=1$, and all the rest have arity $2$.

In a given context, we will extend the lexicon to include additional function and relation symbols with given arity. The most important examples include $+,\cdot,<,\in$ and so forth.

**Definition** A *signature* $\mathcal L$ of first order logic consists of a set of function symbols $\lbrace f_i\rbrace$, a set of relation symbols $\set{R_j}$, and the arities $a(f_i)$ and $a(R_j)$ for all $i,j$.

Given a signature $\mathcal L$, the corresponding *first order lexicon* consists of $\mathcal L$ together with the basic lexicon described above. A first order lexicon is sometimes also called a *language*.

For example, if we are studying group theory then our signature should include a $\cdot$ symbol of arity $2$, if we are studying order theory then our signature should include a $<$ symbol of arity $2$, etc.

With the lexicon established, we naturally wish to focus on just the well-formed expressions in that lexicon, and assign meaning to these well-formed expressions. Unfortunately this is still not always possible. To see this, consider the well-formed expression $+x\forall yz$, which in infix notation translates to $x+(\forall yz)$. Although this is meaningless, you may check that it uses each symbol's arity correctly. (Contrast this with the simpler situation in propositional logic.)

**Definition** Let $\mathcal L=(\lbrace f_i\rbrace,\lbrace R_j\rbrace)$ be a signature of first order logic.

* The *terms* of $\mathcal L$ are the well-formed expressions in the lexicon consisting of just the symbols $f_i$ and $x_n$.
* The *atomic formulas* of $\mathcal L$ are the expressions of the form:  
(1) $R\tau_1\cdots\tau_n$, where $R$ is an $n$-ary relation symbol and $\tau_i$ are terms;  
(2) $\mathord{=}\tau_1\tau_2$ where $\tau_i$ are terms.
* The *well-formed formulas* of $\mathcal L$ are the expressions of the form:  
(1) an atomic formula;  
(2) $\neg\phi$, $\wedge\phi\psi$, $\vee\phi\psi$, $\mathord{\rightarrow}\phi\psi$, or $\mathord{\leftrightarrow}\phi\psi$, where $\phi,\psi$ are well-formed formulas;  
(3) $\forall x\phi$ or $\exists x\phi$ where $x$ is a variable and $\phi$ is a well-formed formula.

Like the definition of well-formed expression, this definition is recursive. The recursive rules serve to place further limitations on precisely which expressions are legal. Our goal is to show that we can assign meaning to the well-formed formulas.

**Example** In lectures we will give several examples of terms, atomic formulas, and more general well-formed formulas. One example would be $\forall x\forall y\mathord{\wedge}\mathord{=}\mathord{+}\mathord{+}xy\mathord{\cdot}\mathord{\cdot} zzw\mathord{\cdot}3x\mathord{>}\mathord{\cdot}xy\mathord{\cdot}xz$, which in infix translates to $(\forall x)(\forall y)(((x+y)+z^2w=3x)\wedge(xy>xz))$. We will analyse which parts are terms, atomic formulas, and well-formed formulas.

In well-formed formulas, as in mathematical statements generally, some of the variables act as parameters while others act as dummy variables. For example consider the statement $(\forall x) x^2\geq y$. This statement is true if $y=0$ and false if $y=1$. But we wouldn't ask what $x$ is, it's just a dummy variable because it's bound by a quantifier.

**Definition** Let $\phi$ be a well-formed formula.

* An occurrence of $x$ in $\phi$ is said to be *bound* if it lies inside the scope of a $\forall x$ or $\exists x$, and *free* otherwise.
* $\phi$ is called a *sentence* if none of the occurrences of variables in $\phi$ are free.

The sentences are the well-formed formulas for which we can conceivably assign a truth value. But as the next examples show, some further context is still needed.

**Example** Consider the (standard infix) sentence $(\exists y)(\forall x)x\leq y$. This sentence is false of real numbers but true of the unit interval $[0,1]$. The sentence says something like, "the universe as it is ordered has an upper bound". But what is the universe, and what is its ordering?

**Example** Consider the (standard infix) sentence $(\forall x)x\geq0\rightarrow(\exists y)y^2=x$. This is true of real numbers but false of rational numbers. This example says "every element of the universe has a square root", but what is the universe and what is a square number?

In order to decide the truth value of a sentence, we still need to know the context of the variables and the behavior of the function and relation symbols in the signature. This package of information is called a *structure* or *model*. A structure is a special type of set which forms one possible universe for sentences in a given signature.

**Definition** Let $\mathcal L$ be a signature of first order logic. An *$\mathcal L$-structure* $\mathcal A$ consists of:

* A nonempty set $A$, the *domain* or *universe* of the structure
* For each $n$-ary function symbol $f$ a function $f^{\mathcal A}\colon A^n\to A$
* For each $n$-ary relation symbol $R$ a relation $R^{\mathcal A}\subset A^n$
* For each $0$-ary function symbol $c$ an element $c^{\mathcal A}\in A$
* For each $0$-ary relation symbol $P$ a truth value $P^{\mathcal A}\in\set{T,F}$

**Example** Let $\mathcal L=\lbrace<\rbrace$ be the signature with one binary relation symbol. Then the rational ordering $(\mathbb Q;<)$ is an $\mathcal L$-structure.

**Example** Let $\mathcal L=\lbrace\cdot\rbrace$ be the signature with one binary function symbol. Then any group $(G;\cdot^G)$, where $G$ is a set and $\cdot^G$ is the gropu operation, is an $\mathcal L$-structure.

**Example** Let $\mathcal L=\set{0,1,+,\cdot,<}$ be the signature with two constant symbols, two binary function symbols, and one binary relation symbol. Then the real ordered field $(\mathbb R;0,1,+,\cdot,<)$ is an $\mathcal L$-structure.

If $\mathcal L$ is a signature, $\alpha$ is an $\mathcal L$-sentence, and $\mathcal A$ is an $\mathcal L$-structure, we can decide whether $\alpha$ is true or false in $\mathcal A$. Thus structures play the same role in first order logic that truth assignments played in propositional logic. We will even use the same symbol $\mathcal A\models\alpha$ when $\alpha$ is true in $\mathcal A$.

The formal definiton of $\models$ is somewhat involved, but it will work the way you might expect. For example, returning to the example sentence $\alpha$ defined by $(\forall x)x\geq0\rightarrow(\exists y)y\cdot y=x$, we will have that $(\mathbb R;+,\cdot,0,1)\models\alpha$ and $(\mathbb Q;+,\cdot,0,1)\not\models\alpha$.

### 5. Semantics, structures, and satisfaction

In this section will formally define of the satisfaction relation $\mathcal A\models\sigma$ for a $\mathcal L$-structure $\mathcal A$ and a sentence $\sigma$. The definition will be done by induction on the subformulas of the sentence $\sigma$. Unfortunately the subformulas of $\sigma$ will not necessarily be sentences! So we will need to address $\mathcal A\models\phi$ in some way even when $\phi$ has free variables.

To get an idea of how this should work, let $\mathcal A$ be the structure $(\mathbb N;+,\cdot,0,1)$ and let $\phi$ be the formula $x^2<10$. We shouldn't define $\mathcal A\models\phi$ to be true or false, because it should depend on the unknown and unquantified value of $x$. We instead define the more complicated statement $\mathcal A\models\phi[x\mapsto a]$, for any $a\in A$. So for instance it should be true that $\mathcal A\models\phi[x\mapsto3]$, and $\mathcal A\not\models\phi[x\mapsto4]$.

The first step in this process should be to deal with the term $x^2$. The definition should understand that $x^2$ evaluates to $9$ when $x\mapsto 3$, and $x^2$ evaluates to $16$ when $x\mapsto 4$. We now introduce notation for evaluating the terms and define how it works in general.

**Definition** Let $\mathcal L$ be a signature of first order logic, and let $\tau$ be a term. Let $\mathcal A$ be an $\mathcal L$-structure and $s$ be function whose domain includes the variables of $\tau$ and whose codomain is $A$. Then:

* If $x$ is a variable of $\tau$, define $\mathrm{val}^{\mathcal A}(x)[s]$ to be $s(x)$
* If $c$ is a constant symbol of $\tau$, define $\mathrm{val}^{\mathcal A}(c)[s]$ to be $c^{\mathcal A}$
* If $\tau=f\tau_1,\ldots,\tau_n$ where $\tau_i$ are terms, define $\mathrm{val}^{\mathcal A}(\tau)[s]=f^{\mathcal A}(\mathrm{val}^{\mathcal A}(\tau_1)[s],\ldots,\mathrm{val}^{\mathcal A}(\tau_n)[s])$.

**Example** Let $\mathcal A$ be the model $(\mathbb N,+,\cdot,0,1)$ and let $\tau$ be the term $x\cdot y$. Let $s$ be the substitution function $x\mapsto 3,y\mapsto 4$. Then:

$$\begin{aligned}
  \mathrm{val}^{\mathcal A}(\tau)[s]
  &=\mathrm{val}^{\mathcal A}(x\cdot y)[s]\\
  &=\mathrm{val}^{\mathcal A}(x)[s]\cdot\mathrm{val}^{\mathcal A}(y)[s]\\
  &=3\cdot 4\\
  &=12
\end{aligned}$$

We next define satisfaction for atomic formulas.

**Definition** Let $\mathcal L$ be a signature of first order logic and $\mathcal A$ be an $\mathcal L$-structure. Let $\phi$ be an atomic formula and let $s$ be a substitution function whose domain includes the variables of $\phi$. Then:

* If $\phi$ is $\mathord{=}\tau_1\tau_2$ then let $\mathcal A\models\phi[s]$ if and only if $\mathrm{val}^{\mathcal A}(\tau_1)[s]=\mathrm{val}^{\mathcal A}(\tau_2)[s]$.
* If $\phi$ is $P$ (a relation symbol of arity $0$), then let $\mathcal A\models\phi$ if and only if $P^{\mathcal A}=T$.
* If $\phi$ is $R\tau_1\cdots\tau_n$, then $\mathcal A\models\phi[s]$ if and only if $(\mathrm{val}^{\mathcal A}(\tau_1)[s],\ldots,\mathrm{val}^{\mathcal A}(\tau_n)[s])\in R^{\mathcal A}$.

Note that in this definition the equality relation is treated specially. This guarantees that the equality relation always represents true equality, and not some alternative model-defined notion of equality.

We finally define satisfaction for general formulas.

**Definition** Let $\mathcal L$ be a signature of first order logic and $\mathcal A$ be an $\mathcal L$-structure. Let $\phi$ be a well-formed formula and let $s$ be a substitution function whose domain includes the variables of $\phi$. Then:

* If $\phi$ is $\neg\alpha$, then let $\mathcal A\models\phi[s]$ is true if and only if $\mathcal A\not\models\alpha[s]$.
* If $\phi$ is $\alpha\wedge\beta$, then let $\mathcal A\models\phi[s]$ if and only if $\mathcal A\models\alpha[s]$ and $\mathcal A\models\beta[s]$
* Similarly, use the truth tables for $\vee,\to,\leftrightarrow$
* If $\phi$ is $\exists x\alpha$, then let $\mathcal A\models\phi[s]$ if and only if there is some $a\in A$ such that $\mathcal A\models\alpha[t]$, where $t$ is the modification of $s$ that sets $x\mapsto a$.
* If $\phi$ is $\forall x\alpha$, then let $\mathcal A\models\phi[s]$ if and only if for all $a\in A$ we have $\mathcal A\models\alpha[t]$, where $t$ is the modification of $s$ that sets $x\mapsto a$.

Observe that if $\sigma$ is a sentence, then no substitution function $s$ is needed. Indeed, anything $s$ specifies will eventually be overwritten by the quantifiers. Thus we can ask whether $\mathcal A\models\sigma$ or $\mathcal A\not\models\sigma$ without any $s$ provided.

**Example** Let $\mathcal A$ be the structure $(\mathbb Q;<)$ and let $\sigma$ be the sentence $(\forall x)(\forall y)(\exists z)x<y\rightarrow x<z<y$. Then the definition implies that $\mathcal A\models\sigma$ if and only if for all $a\in\mathbb Q$ and for all $b\in\mathbb Q$ we have that there exists $c\in\mathbb Q$ such that $\mathcal A\models x<y\rightarrow x<z<y[x\mapsto a,y\mapsto b,z\mapsto c]$. The definition further implies that this will be true if and only if for all $a,b\in\mathbb Q$ there exists $c\in\mathbb Q$ such that $a<b\implies a<c<b$. Finally, this is true since given $a,b$ we can always choose $c=(a+b)/2$.

We often apply the satisfaction relation to a set of sentences.

**Definition** If $\mathcal L$ is a signature of first order logic, then an *$\mathcal L$-theory* is any set of $\mathcal L$-sentences.

**Example** Let $\mathcal L$ consist of one binary function symbol $\cdot$, and let $T$ consist of the following two sentences:

> * $(\forall x)(\forall y)(\forall z)(x\cdot y)\cdot z=x\cdot(y\cdot z)$
> * $(\exists u)(\forall x)x\cdot u=x\wedge u\cdot x=x\wedge(\exists y)x\cdot y=u$

Then $T$ is the *theory of groups* (or group theory for short).

**Example** Let $\mathcal L$ consist of one binary relation symbol $<$, and let $T$ consist of the following sentences:

> * $(\forall x)x\not<x$
> * $(\forall x)(\forall y)x<y\rightarrow y\not<x$
> * $(\forall x)(\forall y)x=y\vee x<y\vee y<x$
> * $(\forall x)(\forall y)(\forall z)x<y\wedge y<z\rightarrow x<z$

Then $T$ is the *theory of linear orders*.

**Example** Let $\mathcal L$ consist of one binary relation symbol $\in$. Let $T$ consist of the axioms of set theory described in section 3. Then $T$ is what we mean when we talk about ZFC.

**Definition** Let $T$ be an $\mathcal L$-theory and let $\mathcal A$ be an $\mathcal L$-structure. We say $\mathcal A\models T$ if for every $\sigma\in T$ we have $\mathcal A\models\sigma$. In this case we also say that $\mathcal A$ is a *model* of $T$.

For example if $T$ is the theory of groups, the models of $T$ are the groups. If $T$ is the theory of linear orders, the models of $T$ are the linear orders. If $T$ is ZFC, the models of $T$ are the possible universes of set theory. This fulfills the notion that model theory provides the universes where a given collection of axioms is true. 

With the concept of first order satisfaction in hand, we can now define several key semantic notions:

**Definition**

* A sentence $\sigma$ is *semantically valid* if for every structure $\mathcal A$ we have $\mathcal A\models\sigma$.
* A theory $T$ *semantically implies* a sentence $\sigma$ if for every structure $\mathcal A$ we have $\mathcal A\models T$ implies $\mathcal A\models\sigma$.
* A theory $T$ is *semantically consistent* there exists a structure $\mathcal A$ such that $\mathcal A\models T$ (a *model* of $T$).

In propositional logic we defined tautologies, which are analogous to valid sentences. In fact, they are a special case. If $\alpha$ is a propositional tautology in $n$ propositoinal variables, then we can make a signature $\mathcal L=\lbrace P_1,\ldots,P_n\rbrace$ where for all $n$, $P_n$ is a relation symbol of arity $0$. Then $\alpha$ is equally a sentence of first order logic, and it is clearly valid.

More generally, we can start with a propositional tautology $\alpha$, and replace each propositional variable symbol with any first order sentence, and the result will be a semantically valid sentence. For example $((\forall x)(\forall y)x^2<y)\vee\neg((\forall x)(\forall y)x^2<y)$ is a valid sentence because it is of the *form* $P\vee\neg P$.

There are also sentences which are semantically valid in a genuinely first order way, that is, they do not just come from propositional tautologies. For example, all of the following are semantically valid: $(\forall x)x=x$; $((\forall x)R(x))\to\neg(\exists x)\neg R(x)$; $((\forall x)\phi(x))\to\phi(\tau)$.

We next give an example of semantic implication. Let $T$ be the theory of groups, and let $\sigma$ be the sentence $(\forall x)(\forall y)(\forall z)xy=xz\rightarrow y=z$. We can recognise $\sigma$ as something that is true in every group. Therefore $T\models\sigma$.

Finally we give examples of consistent and inconsistent theories. The theory of groups is consistent, because we can construct a group and prove that it satisfies the sentences in the theory. Similarly the theory of linear orders is consistent. On the other hand, the theory of non-abelian groups with 5 elements (write this down) is inconsistent, because no such group exists! 

#### First order deductions

Since we have defined semantic implication using satisfaction, you may expect that we will next define syntactic implication using deductions. This means it's time to define deductions or proofs in first order logic. The first order deductions are similar in spirit to the propositional deductions, with the only difference being that the propositional tautologies are replaced by a longer list of valid sentence templates.

**Definition** Let $T$ be a theory, and let $\sigma$ be a sentence. We define $T\vdash\sigma$, read *syntactically implies* $\sigma$, if there exists a sequence of sentences $\sigma_1,\ldots,\sigma_n$ such that $\sigma_n$ is $\sigma$, and for every $i\leq n$ at least one of the following is true:

> (a) $\sigma_i$ is a hypothesis, that is, an element of $T$  
> (b) $\sigma_i$ is an instance of a deductive axiom (described below)  
> (c) $\sigma_i$ follows from two of the previous sentences in $\sigma_1,\ldots,\sigma_{i-1}$ by modus ponens

Next we must state what it means for a sentence to be a deductive axiom. Given our discussion of valid sentences, it might seem natural to allow the deductive axioms to include all the valid sentences. However this has some disadvantages, since it can be difficult to know whether a given sentence is valid or not. Instead we define the deductive axioms to be a selection of the valid sentences which is simultaneously powerful and simple to describe explicitly.

**Definition** A sentence $\sigma$ is a *logical axiom* if it is of one of the following types, plus universal quantifiers at the front.

* A propositional tautology
* Universal instantiation (UI): $\forall x\phi(x)\rightarrow\phi(\tau)$, where $x$ does not occur in $\tau$
* Existential generalization (EG): $\phi(\tau)\to\exists x\phi(x)$, where $x$ does not occur in $\tau$
* Properties of equality: $\forall x\forall y\forall z (x=x)\wedge(x=y\leftrightarrow y=x)\wedge(x=y\wedge y=z\rightarrow x=z)$, and $\forall x\forall y x=y\to f(x)=f(y)$, and $\forall x\forall y x=y\to R(x)\leftrightarrow R(y)$, and the same for symbols of higher arity
* Quantifier duality: $\forall x\neg\phi\leftrightarrow \neg\exists x\phi$
* Quantifier distribution: $\forall x(\phi\to\psi)\to(\forall x\phi\to\forall x\psi)$
* Extra quantifier: $\phi\to\forall x\phi$, where $x$ does not occur free in $\phi$

To explain the statement about additional universal quantifiers at the front, consider the following formula: $((\forall x)(\exists y) x\cdot y=z)\rightarrow((\exists y) 5\cdot y=z)$. This looks like a formula of type UI, but it isn't a sentence. The definition then says that the following is a sentence of type UI: $(\forall z)(((\forall x)(\exists y) x\cdot y=z)\rightarrow((\exists y) 5\cdot y=z))$.

It is easy to see that each of these logical axioms is a valid sentence. While there are vastly more valid sentences not included in the list, we will eventually show that they are all consequences of the ones in the list! Indeed, the list of axioms was selected with this result in mind.

Recall we defined the trio of semantic validity, semantic implication, and semantic consistency using the concept of satisfaction. We have just defined syntactic implication using deductions, and the following completes the syntactic trio of concepts.

**Definition**

* A sentence $\sigma$ is *syntactically valid* if $\emptyset\vdash\sigma$
* A theory $T$ is *syntactically consistent* if $T\not\vdash\sigma\wedge\neg\sigma$. (Any tautological faleshood may be used here.)

**Example** Let $\sigma$ be the sentence $(\forall x)(\exists y)x=y$. We will show that $\sigma$ is syntactically valid, that is, $\emptyset\vdash\sigma$. 

1. $(\forall x)x=x$ (Equality)
2. $(\forall x)(x=x\to (\exists y)x=y)$ (EG)
3. $[(\forall x)(x=x\to (\exists y)x=y)]\to [((\forall x) x=x)\rightarrow ((\forall x)(\exists y)x=y)]$ (Quantifier distribution)
4. $((\forall x) x=x)\rightarrow ((\forall x)(\exists y)x=y)$ (Modus ponens 2,3)
5. $(\forall x)(\exists y)x=y$ (Modus ponens 1,4)

The definition of deduction that we have given is of theoretical value, but not of great practical value. It can be very difficult to take substantial mathematical results and formalize them in this system. In the rest of the section we mention a few tactics for making the work of finding proofs at least somewhat more accessible.

**Theorem** (Deduction theorem) $T\vdash\alpha\to\beta$ if and only if $T\cup\set{\alpha}\vdash\beta$.

*Proof*: The forward implication is just modus ponens. For the reverse implication, assume that $T\cup\set{\alpha}\vdash\beta$ and let $\sigma_1,\ldots\sigma_n$ be a deduction. We will show by induction that for all $i$ we have $T\vdash\alpha\to\sigma_i$.

Assume that $T\vdash\alpha\to\sigma_j$ for all $j<i$. If $\sigma_i$ lies in $T\cup\lbrace\alpha\rbrace$, or is a logical axiom, then it is clear that $T\vdash\alpha\to\sigma_i$. Otherwise $\sigma_i$ followed from earlier items by modus ponens. By inductive hypothesis, we then have $T\vdash\alpha\to\sigma_j$ and $T\vdash\alpha\to(\sigma_j\to\sigma_i)$. It follows using easy tautologies and modus ponens that $T\vdash\alpha\to\sigma_i$. This completes the induction. $\blacksquare$

**Theorem** (Proofs by contradiction) If $T\cup\lbrace\neg\alpha\rbrace\vdash\sigma\wedge\neg\sigma$, then $T\vdash\alpha$.

*Proof*: If $T\cup\lbrace\neg\alpha\rbrace\vdash\sigma\wedge\neg\sigma$, then using propositional tautologies we have $T\cup\lbrace\neg\alpha\rbrace\vdash\alpha$. By the deduction theorem, $T\vdash\neg\alpha\rightarrow\alpha$. By a tautology, $T\vdash\alpha\vee\alpha$ and therefore $T\vdash\alpha$. $\blacksquare$

We invite the reader to verify that the converse of the Proofs by contradiction theorem is also true.

**Theorem** (Universal generalization and existential instantiation) Let $\mathcal L$ be a given signature, and let $c$ be a constant symbol such that $c\notin\mathcal L$.

* (UG) If $T\vdash\phi(c)$, then $T\vdash\forall x\phi(x)$.
* (EI) If $T\cup\set{\phi(c)}\vdash\alpha$, then $T\cup\set{\exists x\phi(x)}\vdash\alpha$.

The UG rule is for proofs that end "... since $c$ was arbitrary, the result holds for all values". The EI rule is for proofs that begin "Since we know one exists, fix a constant $c$ with this property". The proof of the theorem is tedious but not conceptually difficult, we invite you to find it in a reference such as Kunen's book.

**Example** Let $\sigma$ be the sentence $\forall x P(x)\wedge Q(x)\to \forall y P(y)$. We will show that $\sigma$ is syntactically valid, that is, $\emptyset\vdash\sigma$. However rather than providing an explicit deduction, we will mix deduction steps with the results above to show that a deduction exists.

1. We first prove that $\forall x P(x)\wedge Q(x)\vdash\forall y P(y)$.  
    a. $\forall x P(x)\wedge Q(x)$ — (Given)  
    c. $P(c)\wedge Q(c)$ — (UI)  
    d. $P(c)\wedge Q(c)\to P(c)$ — (Tautology)  
    e. $P(c)$ — (MP c,d)  
    g. $\forall y P(y)$ — (UG)  
2. $\forall x P(x)\wedge Q(x)\to \forall y P(y)$ — (Deduction, 1)

### 6. Completeness and compactness

Recall from propositional logic the soundness and completeness theorems, which linked semantic implication and syntactic implication. We now present the analogous result for first order logic.

**Theorem** (Soundness and completeness theorems, version I) Let $T$ be a theory and let $\sigma$ be a sentence. Then $T\models\sigma$ if and only if $T\vdash\sigma$.

The right-to-left implication is the soundness theorem and says anything we can deduce is true, meaning deductions are *sound* reasoning. The proof is just the same as the proof in the case of propositional logic, and simply involves checking that the logical axioms and modus ponens are semantically valid. The left-to-right implication is the completeness theorem.

We will actually study the completeness theorem in another form. Recall that a theory $T$ is syntactically consistent if $T\not\vdash\sigma\wedge\neg\sigma$. Recall also that $T$ is semantically consistent if there exists a model of $T$. 

**Theorem** (Soundness and completeness theorems, version II) $T$ is syntactically consistent if and only if $T$ is semantically consistent.

To see version II implies version I, assume version II is true. Then $T\models\sigma$ if and only if there does not exist a model of $T\cup\lbrace\neg\sigma\rbrace$, which means $T\cup\lbrace\neg\sigma\rbrace$ is semantically inconsistent, which is true if and only if $T\cup\lbrace\neg\sigma\rbrace$ is syntactically inconsistent, which is equivalent to $T\vdash\sigma$ (see the proposition on proofs by contradiction). Thus version I is true. We invite the reader to prove that version I implies version II in a similar fashion.

Thus, proving the completeness theorem is really about building a model. If $T$ is reasonable in the sense that we can't use the sentences of $T$ to deduce a contradiction, then it should be possible to *construct* a model of $T$, that is, a universe in which the sentences of $T$ hold true.

Maybe this makes some intuitive sense to you, but at the same time it should seem like a challenging request. How will we begin to build the model of $T$? The BIG IDEA is to build the model using the terms of the language. In order to illustrate this consider the following.

**Example** Let $\mathcal L=\set{+,0,1,<}$ and let $T$ be the standard axioms of arithmetic of the natural numbers (associativity, commutativity, identity, and so on). Our model will include the terms $0$, $1$, $1+1$, $1+1+1$, etc. These terms are pretty good substitutes for the genuine natural numbers $0$, $1$, $2$, $3$, etc!

Of course there are many other terms such as $1+0+0+1$, should our model include these also? Yes and no. Our theory knows that $1+0+0+1$ is really equivalent to $1+1$. In other words, there is an equivalence relation on the terms given by $\tau_1\sim\tau_2$ if and only if $T\vdash\tau_1=\tau_2$. We will need to work with *equivalence classes* of the terms.

This idea is called a *Henkin construction* or the *Herbrand construction*, named for two mathematicians who contributed to this strategy. In order to begin, we first make a structure from terms.

**Definition** Let $T$ be a theory. The *Henkin structure* $\mathcal H=\mathcal H(T)$ is defined as follows.

* The domain of $\mathcal H$ consists of the equivalence classes $[\tau]$ of $L$-terms $\tau$, with respect to the equivalence relation defined by $\tau_1\sim\tau_2$ if and only if $T\vdash\tau_1=\tau_2$.
* If $f$ is a function symbol, then define $f^{\mathcal H}([\tau_1],\ldots,[\tau_n])$ to be the equivalence class $[f\tau_1\cdots\tau_n]$.
* If $R$ is a relation symbol, then define $([\tau_1],\ldots,[\tau_n])\in R^{\mathcal H}$ if and only if $T\vdash R\tau_1\cdots\tau_n$.

We invite the reader to check that this definition is well-defined, that is, the function values and relation tuples are independent of the equivalence class representatives. This will use the logical proof axioms about equality. We remark that the Henkin structure could equally have been called the Herbrand structure.

The Henkin structure works smoothly for the previous example. The universe will consist of $[0]$, $[1]$, $[1+1]$, etc. Each of these equivalence classes includes infinitely many terms that the theory knows are equal, for instance, $[1]$ includes $1$, $1+0$, $0+(1+0)$, etc. In the structure, $+$ and $\times$ behave as one would expect. So for instance $[1]+[1]=[1+1]$, and more generally all the axioms of $T$ will be true.

But the next example shows that things aren't always this successful.

**Example** Let $\mathcal L_2=\set{+,0,<}$ and let $T_2$ be the standard axioms of arithmetic of the natural numbers. (Whenever an axiom of $T$ says something about the constant $1$, we can write an equivalent axiom of $T_2$ that says it about "the least natural number greater than $0$".) In this language the only terms are $0$, $0+0$, etc, so $\mathcal H$ consists of just one point $[0]$. Thus $\mathcal H(T_2)$ isn't a model of $T_2$.

In order to make examples like this one work, we will have to use terms of an *expanded* language, where constant symbols have been added for every conceivable definition.

**Definition** A theory $T$ is said to have *witnessing terms* if whenever $\phi(x)$ is a formula with one free variable $x$ there exists a term $\tau$ such that $T\vdash\exists x\phi(x)\to\phi(\tau)$.

For example consider the field of real numbers $\mathbb R$. If $\phi(x)$ is $\forall y xy=y+y$ then a witnessing term would be $1+1$. If $\phi(x)$ is $x\cdot x=1+1$ then there is no witnessing term so we will need to add one. The following is the next key to Henkin/Herbrand construction.

**Lemma** If $T$ is a syntactically consistent theory, then there exists a syntactially consistent theory $T'$ in an expanded language such that $T\subset T'$ and $T'$ has witnessing terms.

*Proof*: We first show how to add a witnessing term for a single formula $\exists x\phi(x)$. To do this, we let $\mathcal L'=\mathcal L\cup\set{c}$, and let $T'=T\cup\set{\exists x\phi(x)\to\phi(c)}$.

We claim that $T'$ is syntactically consitent. If it isn't, then there is a proof from $T'$ of a contradictory sentence $\alpha\wedge\neg\alpha$. By the proof-by-contradiction theorem, there is a proof from $T$ of $\neg(\exists x\phi(x)\to\phi(c))$. Using a tautology, there is a proof from $T$ of $\exists x\phi(x)$ and a proof from $T$ of $\neg\phi(c)$. By UG, there is a proof from $T$ of $\forall x\neg\phi(x)$. This is clearly a contradiction (quantifier duality), establishing the claim.

Now to add witnessing terms for all formulas, we inductively define $\mathcal L^{(n)},T^{(n)}$ as follows. First let $\mathcal L^{(0)}=\mathcal L$ and $T^{(0)}=T$. If $\mathcal L^{(n)},T^{(n)}$ have been defined, we let $\mathcal L^{(n+1)}$ include new constant symbols for each existential formula of $\mathcal L^{(n)}$, and let $T^{(n+1)}$ include corresponding sentences for each. Then by an argument similar to the above, each $T^{(n)}$ is syntactically consistent, and it follows that $T'=\bigcup T^{(n)}$ is syntactically consistent. Moreover with $T'$ we have "caught our tail" meaning that $T'$ has witnessing terms. $\blacksquare$

In the last example with $0$ in the language but not $1$, the theory $T_2$ proves that there exists a least element greater than $0$, so when we go to $T_2'$ we will get a new constant symbol for $1$. For that matter we will get constant symbols for $2$, $3$, etc. When we construct $\mathcal H(T_2')$ we will indeed get a model of $T_2$.

But the next and final example shows there is one more issue to consider.

**Example** Let $\mathcal L=\set{<,a,b}$, where $a,b$ are constant symbols, and let $T$ be the theory of linear orders, together with the sentence $a\neq b$. Then $\mathcal H$ has domain $\set{a,b}$. The theory doesn't prove either $a<b$ or $b<a$, so $\mathcal H$ won't satisfy either of these. Thus $\mathcal H$ is not a model of $T$, because it doesn't satisfy the trichotomy axiom.

The problem in this example is that the theory $T$ doesn't say much about its terms. To fix this last issue, we will work with theories that say as much as they can.

**Definition** A theory $T$ is *complete* if for every sentence $\sigma$ we have either $\sigma\in T$ or $\neg\sigma\in T$.

The next result says that an incomplete theory can always be *extended* to a complete theory. This is done by making a bunch of arbitrary decisions about what sentences to add, in a process similar to the proof of the propositional compactness theorem.

**Lemma** If $T$ is a syntactically consistent theory, there exists a complete syntactically consistent theory $\bar T$ such that $T\subset\bar T$.

*Proof*: We first say how to extend $T$ by one more sentence. Let $\sigma$ be a sentence such that both $\sigma$ and $\neg\sigma$ are not elements of $T$. If $T\vdash\sigma$, then $T\cup\lbrace\sigma\rbrace$ is clearly consistent. If $T\not\vdash\sigma$, then $T\cup\lbrace\neg\sigma\rbrace$ will be consistent (check this!).

Now iterate the procedure until there are no more sentences $\sigma$ such that both $\sigma$ and $\neg\sigma$ are not elements of $T$. The resulting theory $\bar T$ will be consistent and complete. $\blacksquare$

Referring back to the last example, if we extend $T$ to $\bar T$ then we must add one of the sentences $a<b$ or $b<a$ to $\bar T$. Thus the resulting Henkin structure of $\bar T$ will be a linear order and in particular a model of $T$.

We are finally ready to use the Henkin construction to prove the completeness theorem.

**Theorem** (Completeness Theorem, version II) If $T$ is syntactically consistent, then $T$ has a model.

*Proof*: We apply the lemmas we have proved in sequence. Given $T$, we first extend it to a theory with witnessing terms in an expanded language, and then further extend it to a complete theory $T^\ast$ in the expanded language. We then let $\mathcal H$ be the Henkin structure of $T^\ast$. 

We claim that for all sentences $\sigma$ we have $\sigma\in T^\ast$ if and only if $\mathcal H\models\sigma$, so that $\mathcal H$ really is a model of $T^\ast$ and therefore of $T$. We will proceed by induction on the *complexity* of $\sigma$. For this we can assume that the only connectives in $\sigma$ are $\wedge,\neg,\exists$, and proceed by induction on the number of occurrences of these symbols.

First assume $\sigma$ is an atomic sentence $R\tau_1\cdots\tau_n$. Then the desired result follows from the definition of the relations of $\mathcal H$. (There is actually a subtle point that we must check $\mathrm{val}^{\mathcal H}(\tau)=[\tau]$ for all terms $\tau$. This is an induction on the construction of $\tau$ using the definition of $\mathcal H$ for the base case.)

Next if $\sigma$ is of the form $\neg\alpha$, then the result follows from the inductive hypothesis for $\alpha$ and the completeness of $T^\ast$. Indeed, we have $\sigma\in T^\ast$ iff $\alpha\notin T^\ast$ iff $\mathcal H\not\models\alpha$ iff $\mathcal H\models\sigma$. Similarly if $\sigma$ is of the form $\alpha\wedge\beta$ then the result is immediate from the inductive hypothesis for $\alpha$ and $\beta$ and the completness of $T^\ast$.

Finally if $\sigma$ is of the form $\exists x\phi(x)$ then since $T^\ast$ has witnessing terms there is a term $\tau$ in the expanded language such that the sentence $\exists x\phi(x)\to\phi(\tau)$ is in $T^\ast$. Now:

$$\begin{aligned}
  \sigma\in T^\ast &\implies \phi(\tau)\in T^\ast & \text{completeness of $T^\ast$}\\
  &\implies \mathcal H\models\phi(\tau) & \text{inductive hypothesis}\\
  &\implies \mathcal H\models\sigma
\end{aligned}$$

And conversely:

$$\begin{aligned}
  \mathcal H\models\sigma &\implies \mathcal H\models\phi(\tau) &\text{for some term $\tau$ :)}\\
  &\implies \phi(\tau)\in T^\ast &\text{inductive hypothesis}\\
  &\implies T^\ast\vdash\sigma &\text{EG}\\
  &\implies \sigma\in T^\ast &\text{completeness of $T^\ast$}
\end{aligned}$$

This completes the proof. $\blacksquare$.

We remark that the :) follows from the definition of the Henkin structure. Since we don't have control over the length of the term $\tau$, we had to do our induction over the complexity of $\sigma$ instead of the length of $\sigma$.

The completeness theorem has many consequences, as we shall soon see. But the most obvious consequence is that it greatly simplifies our terminology:

* Semantic validity is equivalent to syntactic validity.
* Semantic implication is equivalent to syntactic implication.
* Semantic consistency is equivalent to syntactic consistency.

As a result we rarely need to discern between the semantic and syntactic notions.

#### Compactness

To further explore the consequences of the completeness theorem, we now introduce the compactness theorem for first order logic.

**Theorem** (Compactness theorem) If every finite subset of $T$ has a model, then $T$ has a model.

We invite the reader to verify that similarly to the propositional completeness and compactness theorems, the first order completeness and compactness theorems are equivalent to each other in the sense that there exist short proofs in both directions.

As we have seen, the propositional compactness theorem is useful in taking statements about finite objects which are arbitrarily large to statements about infinite objects. The first order compactness theorem has a similar set of applications. The following corollary was stated in Section 1; here we give a first order version of the same argument.

**Corollary** Let $G$ be a combinatorial graph with adjacency relation $\sim$. Suppose that every finite subgraph $G_0\subset G$ has a proper coloring with $n$ colors. Then $G$ has a proper coloring with $n$ colors.

*Proof*: Let the language $\mathcal L$ consist of a binary relation $\sim$, constant symbols $c_v$ for every $v\in G$, and unary relation symbols $P_1,\ldots,P_n$. Let the theory $T$ consist of the following axioms:

* $c_v\neq c_{v'}$ whenever $v\neq v'$
* $c_v\sim c_{v'}$ whenever $v\sim v'$
* $c_v\not\sim c_{v'}$ whenever $v\not\sim v'$
* $\forall x P_1(x)\vee\cdots\vee P_n(x)$
* $\forall x \bigwedge_{i\neq j} \neg P_i(x)\wedge P_j(x)$
* $\forall x\forall y x\sim y\to \bigwedge_i\neg P_i(x)\wedge P_i(y)$

Then every finite subset of $T$ is consistent. Indeed, if $T_0$ is a finite subset of $T$, then $T_0$ mentions a certain subset $G_0\subset G$. The induced subgraph corresponding to $G_0$ is bipartite and thus gives rise to a model of $T_0$.

By the compactness theorem, $T$ has a model, $G'$. Observe that $G$ is a subgraph of $G'$ via the function which sends any $v\in G$ to the interpretation of $c_v$ in $G'$. Since $G'$ is bipartite, it follows that $G$ is bipartite. $\blacksquare$

### 7. Applications of compactness, more about theories

We have just seen that the compactness theorem for first order logic has similar applications to the compactness theorem for propositional logic. In this section we begin by exploring some of the more distinctly first order applications of the first order compactness theorem.

**Corollary** Suppose $T$ has arbitrarily large finite models. Then $T$ has infinite models.

*Proof*: Let $\sigma_n$ be the sentence which says that there exist $n$ distinct elements of the universe. That is, $\sigma_n$ says that $\exists x_1\cdots\exists x_n\bigwedge x_i\neq x_j$. Let $T'$ be the theory $T\cup\set{\sigma_n:n\in\mathbb N}$. Then every finite subset of $T'$ is consistent by our hypothesis. As a consequence $T'$ is consistent. Any model of $T'$ is a model of $T$ and is infinite. $\blacksquare$

This simple idea can also be used to derive many further consequences. The first is key in the theory of *nonstandard arithmetic*, where one studies models of number theory with infinite elements, and the second fact is key in *nonstandard analysis* where one studies models of analysis with infinitesimal elements.

**Corollary** Let $T$ be the theory of the natural numbers, that is, the set of sentences true in the structure $(\mathbb N;+,\times,<,0,1)$. There is a model of $T$ with an element $N$ such that $n<N$ for all $n\in\mathbb N$.

**Corollary** Let $T$ be the theory of the real numbers, that is, the set of sentences true in the structure $(\mathbb R;+,\times,<,0,1)$. There is a model of $T$ which contains $\mathbb R$ and an element $\epsilon$ such that for all $0<r\in\mathbb R$ we have $0<\epsilon<r$.

We invite the reader to fill in the proofs of these results.

For each theory $T$ there is a corresponding class of models of $T$. We will say that a class $\mathcal C$ of structures is *axiomatizable* if there exists a theory $T$ such that the models of $T$ are precisely the elements of $\mathcal C$. It is natural to ask whether every (reasonable) class of srtuctures is axiomatizable. Our next result says that the answer is no.

Recall that a graph is *connected* if for any two vertices $x,y$, there exists a path from $x$ to $y$. That is, for any $x,y$ there is a sequence of vertics $x_1,\ldots,x_n$ such that $x\sim x_1\sim x_2\sim\cdots\sim x_n=y$.

**Corollary** The class of connected graphs is not axiomatizable.

*Proof*: Suppose there exists a theory $T$ such that the models of $T$ are exactly the connected graphs. Expand the language with two new constant symbols $a,b$. Let $\sigma_n$ be the sentence which says there is no path from $a$ to $b$ of length $n$. Let $T'$ be the theory $T\cup\set{\sigma_n:n\in\omega}$. Then any finite subset $T_0\subset T'$ is consistent. Indeed, if $N$ is the largest number such that $\sigma_N$ occurs in $T_0$, then a graph consisting of a single path of length $N+1$ from $a$ to $b$ gives a model of $T_0$. It follows from the compactness theorem that $T'$ is consistent and hence has a model. But any model of $T'$ is disconnected, because there cannot be a path from $a$ to $b$. Hence we have shown that there is a disconnected model of $T$, a contradiction. $\blacksquare$

**Corollary** The class of well-orders is not axiomatizable.

*Proof*: Suppose there exists a theory $T$ such that the models of $T$ are exactly the well-orders. Expand the language with new constant symbols $c_n$ for $n\in\omega$. Let $\sigma_n$ be the sentence which says that $c_n<\cdots<c_0$. Let $T'$ be the theory $T\cup\set{\sigma_n:n\in\omega}$. Then any finite subset $T_0\subset T'$ is consistent. Indeed, if $N$ is the largest number such that $\sigma_N$ occurs in $T_0$, then the structure $(\omega,<)$ together with a decreasing sequence of interpretations of $c_0,\ldots,c_n$ is a model of $T_0$. It follows from the compactness theorem that $T'$ is consistent and hence has a model. But any model of $T'$ is ill-founded, because the interpretations of the $c_n$ form an infinite decreasing sequence. Hence we have shown that there is an ill-founded model of $T$, a contradiction. $\blacksquare$

Before beginning the next series of results, we need a brief refresher on cardinality in set theory. Before starting in on cardinality, first recall that the von Neumann natural numbers $0,1,2,\ldots$ may be followed up by von Neumann ordinal numbers $\omega,\omega+1,\ldots,\omega+\omega,\omega+\omega+1,\ldots$.

The von Neumann natural numbers have the property that each $n$ is not in bijection with any $m<n$, that is, its cardinality is larger. However $\omega+1$ is in bijection with $\omega$, and so are many more ordinals after it. How long will the sequence of ordinals continue until we reach an ordinal so large that it isn't in bijection with $\omega$? It's unclear but it must happen.

We say that an ordinal $\kappa$ is a *cardinal number* if $\kappa$ is not in bijection with any ordinal $\alpha<\kappa$. The cardinal numbers are thus very special ordinals that occur unboundedly but in some sense rarely.

It is not difficult to prove using AC that for any set $A$, there exists an ordinal $\alpha$ such that $\alpha$ is in bijection with $A$. The *cardinality* of $A$ is the least ordinal $\kappa$ that is in bijection with $A$. We sometimes write $\vert A\vert=\kappa$. Thus if $A$ is infinite and countable we have $\vert A\vert=\omega$. But if $A$ is uncountable then there will be some larger cardinal $\kappa$ such that $\vert A\vert=\kappa$.

When talking about $\omega$ in the context of cardinality, we give it the special name $\aleph_0$, because it is the first in the sequence of infinite cardinals. We let $\aleph_1$ denote the second infinite cardinal, $\aleph_2$ the third, and so on.

We say that a set $A$ is *countable* if its cardinality is $\leq\aleph_0$, and *uncountable* if its cardinality is $\geq\aleph_1$. (Sometimes people use the term countable to mean *countably infinite*, or cardinality exactly $\aleph_0$.)

Cardinal numbers may be added using disjoint unions, and multiplied using cartesian products. For instance, if $\kappa$ and $\lambda$ are cardinals, then $\kappa\cdot\lambda$ is defined as the cardinality of the cartesian product $\vert\kappa\times\lambda\vert$. One should check that for finite cardinals (natural numbers), this gives the expected results. But if one of the two cardinals is infinite, $\kappa\cdot\lambda$ will always be $\max(\kappa,\lambda)$.

Returning to theories in logic, we have shown above that theories with arbitrarily large finite models have infinite models. Now it is natural to ask what cardinalities will occur. The next result addresses this question with the most expansive answer possible.

**Theorem** (Lowenheim–Skolem thoerem) Suppose $\mathcal L$ is a finite or countable signature, $T$ is an $\mathcal L$-theory, and $T$ has an infinite model. Then for any infinite cardinal $\kappa$, $T$ has a model of cardinality $\kappa$.

*Proof*. Assume $T$ has an infinite model and let $\kappa$ be given. Expand the signature to include $\kappa$ many constant symbols $c_\alpha$ for $\alpha<\kappa$. Let $T'=T\cup\set{c_\alpha\neq c_\beta:\alpha\neq\beta}$. Then any finite subset $T_0\subset T'$ is consistent. Indeed, $T_0$ mentions just finitely many of the constant symbols $c_\alpha$, and we can intrepret them as arbitrary elements of the given model of $T$. It follows that $T'$ is consistent, and therefore by the compactness theorem $T'$ has a model. Clearly this model will have size at least $\kappa$.

But we want it to have size exactly $\kappa$. Instead of using compactness, use the proof of the completeness theorem to build the Henkin structure $\mathcal H$ in the expanded language. The expanded language has $\kappa$ many terms, and since the $c_\alpha$ will be in distinct equivalence classes, it has exactly $\kappa$ many terms. Thus $\mathcal H$ is a model of $T$ of size $\kappa$. $\blacksquare$

The Lowenheim–Skolem theorem has the mind-bending consequence that if ZFC is consistent, then ZFC has a countable model. Since we know that ZFC implies there exist uncountable sets, we appear to have reached a paradox: an uncountable object is contained in a countable object. The resolution to this apparent contradiction is that the countable model only believes its sets are uncountable because it lacks the bijections to prove they are countable. These bijections do exist but externally to the model.

#### Complete theories

Previously we said that a theory $T$ is complete if it is consistent, and for every sentence $\sigma$ either $\sigma\in T$ or $\neg\sigma\in T$. We sometimes abuse the term and say that $T$ is complete if its deductive closure is complete, that is, if for all sentences $\alpha$, $T\vdash\alpha$ or $T\vdash\neg\alpha$.

**Definition**. Let $\mathcal A$ be any structure. The *theory* of $A$, written $\mathrm{Th}(\mathcal A)$, is the set of sentences $\sigma$ such that $\mathcal A\models\sigma$.

It follows from the definition of satisfaction that $\mathrm{Th}(\mathcal A)$ is always a complete theory. For instance the theory of natural numbers $\mathrm{Th}(\mathbb N;+,\times)$ and the theory of real numbers $\mathrm{Th}(\mathbb R;+,\times)$ are complete theories.

In accordance with common practice, we usually say that $T$ is complete if the set of logical consequences of $T$ is complete. That is, $T$ is *complete* if it is consistent and for every sentence $\sigma$ either $T\models\sigma$ or $T\not\models\sigma$.

For example, if $T$ is the theory which says that $G$ is a group with exactly $7$ elements, then $T$ is complete. (One shows in a standard algebra class that there is only one such group.)

On the other hand, most theories are not complete. For example, if $T$ is the theory of infinite linear orders then $T$ is not complete. (Is there a last element? Consider $(0,1)$ versus $(0,1]$.) For another example, if $T$ is the theory of infinite abelian groups then $T$ is not complete. (Are all elements of the group divisible by 2? consider $\mathbb Z$ versus $\mathbb Q$.) These theories are not meant to be complete because the point is to study the diversity of models.

Generally we can show $T$ is not complete by finding sentences $\sigma$ such that $T\cup\set{\sigma}$ has a model, so $\neg\sigma$ is not a consequence of $T$, and $T\cup\set{\neg\sigma}$ has a model, so $\sigma$ is not a consequence of $T$.

But how can one show that a given theory $T$ *is* complete? In general this can be a challenging problem, but in the rest of this section, we discuss one relatively easy tool to prove that a theory is complete. We first need several new definitions.

**Definition** Structures $\mathcal A,\mathcal B$ are *isomorphic* if there is a bijection $\phi\colon A\to B$ such that for every function symbol $f$ we have $f^{\mathcal A}(a)=b\iff f^{\mathcal B}(\phi(a))=\phi(b)$ and for every relation symbol $R$ we have $R^{\mathcal A}(a)\iff R^{\mathcal B}(\phi(a))$.

**Definition** Structures $\mathcal A,\mathcal B$ are *elementarily equivalent* if they satisfy the same sentences: $\mathcal A\models\sigma\iff\mathcal B\models\sigma$. In other words, $\mathrm{Th}(\mathcal A)=\mathrm{Th}(\mathcal B)$.

Since isomorphisms preserve every property of the structure, it is clear that if $\mathcal A,\mathcal B$ are isomorphic then they are elementarily equivalent. We also know that the converse is false as we have seen several examples of properties of a structure which cannot be described in logic. Of course, if $T$ is a complete theory with infinite models, then by Lowenheim--Skolem $T$ will have models of two different cardinalities, which must be non-isomorphic.

This example suggests we should confine ourselves to looking at two different models of $T$ of the same cardinality, and ask whether they must be isomorphic to each other. This leads to the following definition.

**Definition** Let $T$ be a theory and let $\kappa$ be an infinite cardinal. Then $T$ is called *$\kappa$-categorical* if all models of $T$ of cardinality $\kappa$ are isomorphic to one another.

Most complete theories $T$ will not be $\kappa$-categorical for most $\kappa$. For example, we have seen the natural numbers and the "nonstandard" natural numbers are two models of the theory of natural numbers with very different properties.

But some theories are categorical in one cardinality or another. The following is the most famous example of a categorical theory. The theory of *dense linear orders without endpoints* consists of the theory of linear orders plus the axioms: $(\forall x)(\forall y)(\exists z)x<y\rightarrow x<z<y$, and $(\forall x)(\exists y)(\exists z)y<x<z$. Thus the rational order $(\mathbb Q;<)$ is an example of a dense linear order without endpoints.

**Proposition** The theory $T$ of dense linear orders without endpoints is $\aleph_0$-categorical.

*Proof sketch*: Let $\mathcal A,\mathcal B$ be two countable models $T$. Let $a_n$ enumerate $A$ and let $b_n$ enumerate $B$. We can recursively construct an isomorphism using the "back-and-forth" method. Initially let $\phi(a_0)=b_0$. Next assume $\phi$ has been defined on $a_0,\ldots,a_n$ and $\phi^{-1}$ has been defined on $b_0,\ldots,b_n$. We then define $\phi$ on $a_{n+1}$ and $\phi^{-1}$ on $b_{n+1}$ by mapping them to the interval required to preserve the order relations. $\blacksquare$

Note that the theory of dense linear orders without endpoints is not $\kappa$-categorical for $\kappa=2^{\aleph_0}$. For example $\mathbb R$ and $\mathbb R\setminus\set{0}$ are dense linear orders without endpoints that are not isomorphic to one another.

Next we describe an example of a theory that is $\kappa$-categorical for some uncountable $\kappa$. A group is called torsion-free if it satisfies $\forall x x\neq0\rightarrow nx\neq 0$. A group is called divisible if it satisfies $\forall x\exists y nx=y$. The torsion-free divisible abelian groups are simply direct sums of copies of $\mathbb Q$. 

**Proposition.** The theory $T$ of torsion-free divisible abelian groups is $\aleph_1$-categorical.

*Proof*: Any torsion-free divisible abelian group $G$ can be made into a rational vector space by defining $\frac mng=h$ iff $mg=nh$. Note that divisibility is used to show there is such an $h$, and torsion-free is used to show that $h$ is unique. Now any two vector spaces of cardinality $\aleph_1$ over a field of cardinality $\aleph_0$ must have dimension $\aleph_1$, and therefore they are isomorphic to one another. $\blacksquare$

The following result shows the connection between categorical and complete theories.

**Thoerem** (Vaught test) Let $T$ be a consistent theory in a finite language with no finite models. If $T$ is $\kappa$-categorical for some $\kappa$, then $T$ is complete.

*Proof*: Suppose that $T$ is $\kappa$-categorical but not complete. Then there is a sentence $\sigma$ such that both $T\cup\lbrace\sigma\rbrace$ and $T\cup\lbrace\neg\sigma\rbrace$ are consistent. By the Lowenheim–Skolem theorem, there are models $\mathcal A,\mathcal B$ of $T\cup\lbrace\sigma\rbrace,T\cup\lbrace\neg\sigma\rbrace$ respectively, of cardinality $\kappa$. This contradicts that $T$ is $\kappa$-categorical. $\blacksquare$

**Corollary** The theory of dense linear orders without endpoints is complete. In particular, $(\mathbb Q,<)$ and $(\mathbb R,<)$ are elementarily equivalent.

**Corollary** The theory of torsion-free divisible abelian groups is complete. In particular, $(\mathbb Q,+)$ and $(\mathbb R,+)$ are elementarily equivalent.

A famous theorem of Morley states that a theory $T$ is $\kappa$-categorical for some $\kappa\geq\aleph_1$ if and only if $T$ is $\aleph_1$-categorical. This means that there are just two types of categoricity, countable and uncountable.

## Part III: Computability theory and incompleteness

#### Introduction

In Part II we said that most theories $T$ are incomplete, like the theory of linear orders and the theory of groups. In these examples the incompletness is a feature and not a bug, because in these examples we wish to study the diversity of models.

On the other hand, when a theory is foundational, it may be desirable for it to be complete. Some important theories in mathematics that are complete include the laws of addition of natural numbers, the theory of "real closed" fields (like $\mathbb R$), and the theory of algebraically closed fields of characteristic zero (like $\mathbb C$). (We won't prove these results here).

But the most general foundational theories, such as the theory of arithmetic and the theory of sets, turn out to be incomplete. In this part we give a brief introduction to Godel's Incompleteness Theorem, which is a very general result that explains why this must be the case.

### 8. Definability, absoluteness, and decidability

Before we can state the incompleteness theorem, we need to introduce the notions of definability and decidability.

Beginning with definability, we first recall the following definition.

**Definition** Let $\mathcal A$ be a structure.

* An $n$-ary relation $R\subset A^n$ is *definable* if there is a formula $\phi(x_1,\ldots,x_n)$ such that $(a_1,\ldots,a_n)\in R\iff\mathcal A\models\phi[x_i\mapsto a_i]$.
* An $n$-ary function $f\colon A^n\to A$ is *definable* there is a formula $\phi(x_1,\ldots,x_n,y)$ such that $f(a_1,\ldots,a_n)=b\iff\mathcal A\models\phi[x_i\mapsto a_i,y\mapsto b]$.
* An element $a\in A$ is *definable* if there is a formula $\phi(x)$ such that $b=a\iff A\models\phi[x\mapsto a]$.

**Example** Let $\mathcal A=(\mathbb N;+)$. Then $0$ is definable using the formula $x+x=x$, and $<$ is definable using the formula $(\exists z)x+z=y$. We invite the reader to show that $1$ is definable and in fact every element of $\mathbb N$ is definable. (It's also worth thinking about the harder question: is $\times$ definable?)

**Definition** Let $T$ be an $\mathcal L$-theory, and $\phi$ a formula with free variables $x_1,\ldots,x_n$. Let $\mathcal L'=\mathcal L\cup\lbrace R\rbrace$, where $R$ is a new relation symbol. The *expansion by definitions* of $T$ with $\phi$ is the $\mathcal L'$-theory $T'=T\cup\set{\phi(x_1,\ldots,x_n)\iff R(x_1,\ldots,x_n)}$.

It is not difficult to show using surgery on deductions that if $T'$ is an expansion by definitions of $T$, then $T,T'$ prove exactly the same $\mathcal L$-sentences. Moreover if $\phi'$ is any $\mathcal L'$-formula then $T'$ proves that $\phi'$ equivalent to an $\mathcal L$-formula $\phi$. Finally, if $\mathcal A$ is any model of $T$ then $\mathcal A$ can be made into a model of $T'$ by interpreting the symbols of $\mathcal L'$ according to their definitions.

**Example** Continuing the example above, the structure $(\mathbb N;+,<,0,1)$ is an expansion of the structure $(\mathbb N;+)$ using the definitions provided. In this sense it contains no more information than $(\mathbb N;+)$.

In the rest of this section we study definability in models of set theory. That is, we will return to our favorite theory ZFC and its sub-theories. Something potentially confusing happens when we study models of set theory that doesn't happen with other theories: we can try to use a set with its true $\epsilon$ relation as a model of set theory.

**Definition** Let $A$ be any set. Then $A$ gives rise to a *set model* $(A;\epsilon)$ with domain $A$ and binary relation $\epsilon$.

When we work with set models, we skip the structure notation $\mathcal A=(A;\epsilon)$ and simply write $A$. Of course most set models will not satisfy all of ZFC, but some sub-theory of ZFC. For instance, every set model satisfies Extensionality. The set $\mathbb N$ doesn't satisfy pairing because for instance $(0,1)=\lbrace1,2\rbrace$ isn't a natural number.

One of the most useful set models is HF, the set of hereditarily finite sets. (In references, this may also be denoted as $V_\omega$ or $\mathcal R_\omega$.) It is an exercise to check that HF satisfies all of ZFC except Infinity. Similarly the set model HC consisting of the hereditarily countable sets satisfies all of ZFC except Power Set.

When $A,B$ are set models and $A\subset B$, both models believe they are talking about some of the same objects (they share the elements of $A$ in common), but they may disagree about properties of these objects. For example consider $\mathbb N$ and HF. We have $\mathbb N\subset HF$. Both these set models agree on which object is the empty set, but they disagree on whether $\epsilon$ is a linear order or not. An even worse example is $\set{3,4,5,\ldots}$, which disagrees with $\mathbb N$ and HF about which object is the empty set!

**Definition** Let $A,B$ be sets such that $A\subset B$. A formula $\phi(x_1,\ldots,x_n)$ is *absolute* between $A$ and $B$ if for all substitution functions $s\colon\lbrace x_1,x_2,\ldots\rbrace\to A$ we have $A\models\phi[s]\iff B\models\phi[s]$.

Which formulas are absolute between which set models? This is a complicated question in general, but there is a large class of formulas that is absolute between any two set models which are transitive. Recall that a set $A$ is *transitive* if $b\in a\in A$ implies $b\in A$.

**Definition** A formula $\phi$ is called a *$\Delta_0$-formula* if its quantifiers are bounded, that is, every occurrence of $\exists$ is of the form $\exists y\in z$ and every occurrence of $\forall$ is of the form $\forall y\in z$.

The notation $\exists y\in z$ and $\forall y\in z$ aren't technically part of our first order logic. Instead these are abbreviations: $(\exists y\in z)\cdots$ is short for $(\exists y)y\in z\wedge\cdots$, and $(\forall y\in z)\cdots$ is short for $(\forall y)y\in z\rightarrow\cdots$.

**Example** The statement that $x$ is an ordered pair may be expressed as a $\Delta_0$-formula. One needs to say something like $(\exists a)(\exists b) x=(a,b)$, but these quantifiers are not bounded. In fact $a,b$ are found somewhere inside the structure of $x$: $(\exists y\in x)(\exists z\in x)(\exists a\in z)(\exists b\in z)x=\lbrace y,z\rbrace\wedge y=\lbrace a\rbrace\wedge z=\lbrace a,b\rbrace$.

On the other hand, the proposition that $x$ is a power set of another set cannot (apparently) be expressed as a $\Delta_0$-formula. Here one wishes to let $\phi(x)$ say $(\exists y)(\forall z)(z\in y\leftrightarrow z\subset x)$ but these quantifiers are unbounded and in fact cannot be completely eliminated.

**Theorem** If $A,B$ are transitive sets and $A\subset B$, then for any $\Delta_0$-formula $\phi$ we have that $\phi$ is absolute between $A$ and $B$.

*Proof*: We use induction on the complexity of $\phi$. If $\phi$ is atomic then it is of the form $x=y$ or $x\in y$. In each case the absoluteness holds because both $A$ and $B$ are using the true equality and element relations.

If $\phi$ is $\neg\alpha$ then the inductive hypothesis for $\alpha$ clearly gives the corresponding statement for $\phi$. A similar argument holds for the binary connectives.

If $\phi$ is $(\exists y\in z)\alpha$ and the statement is true of $\alpha$ then we have:

$$\begin{aligned}
A\models (\exists y\in z)\alpha[s]
  &\iff A\models (\exists y)y\in z\wedge\alpha[s]\\
  &\iff \exists a\in A\ A\models y\in z\wedge\alpha[s,y\mapsto a]\\
  &\iff \exists a\in B\ B\models y\in z\wedge\alpha[s,y\mapsto a]\\
  &\iff B\models (\exists y)y\in z\wedge\alpha[s]\\
  &\iff B\models (\exists y\in z)\alpha[s]
\end{aligned}$$

Here in the backwards direction we are using transitivity to say that if $a\in B$ and $a$ is required to be in $s(z)\in A$, then $a\in A$. $\blacksquare$

#### Decidability

Let us now work with the set model HF. Informally, we say that $A$ is *decidable* if there is a procedure that decides for any given $a\in HF$ whether $x\in A$ or $x\notin A$. In other words, there should be an algorithm or computer program which takes input $x$ and halts and outputs Yes if $x\in A$ and halts and outputs No if $x\notin A$.

For example, if $\phi$ is a $\Delta_0$-formula, let $A=\set{a\in HF:A\models\phi[x\mapsto a]}$ be the set corresponding $\Delta_0$-definable subset. Then $A$ is very simple in the sense that there is a natural decision procedure to decide whether or not $x\in A$. One simply steps through the formula testing its conditions, and each time one encounters a bounded quantifier, one must initiate a finite search. Note that this wouldn't work for unbounded quantifiers, because a naive infinite search will never terminate.

On the other hand, there are sets that are intuitively decidable but not $\Delta_0$-definable. For example, let $A$ be the set of even natural numbers. Then there is cleary a decision procedure for $A$: given $a$ first check whether $a\in\mathbb N$ (that is, $a$ is totally ordered by $\in$ and a transitive set). Then mark off elements in pairs until you have $0$ or $1$ elements left over. But $A$ is not $\Delta_0$-definable. To show this, note that if it were, then since $\mathbb N\subset HF$ is transitive, $A$ would be definable in $\mathbb N$ using only $\in$.

But this is impossible. We have seen using compactness that $\mathrm{Th}(\mathbb N)$ has a model $\mathcal N$ with "nonstandard" elements. In such a model, $A^{\mathcal N}$ still occupies "every other" standard and nonstandard element. But the model has an automorphism $f$ that shifts every non-standard element one unit to the right. Since $f(A^{\mathcal N})\neq A^{\mathcal N}$, we must have that $A^{\mathcal N}$ is not definable and finally that $A$ is not definable.

The next definition helps us go beyong $\Delta_0$ to further levels of definability.

**Definition** A formula $\phi$ is $\Sigma_1$ if it is of the form $\exists y\alpha$, where $\alpha$ is $\Delta_0$. A formula $\phi$ is $\Pi_1$ if it is of the form $\forall y\alpha$, where $\alpha$ is $\Delta_0$.

We remark that it is also permitted to use several quantifiers of the same type, so if $\alpha$ is $\Delta_0$ then $\exists y\exists z\alpha$ is $\Sigma_1$ too. But it's technically not necessary because we can always replace a double quantifier with a single quantifier over a pair $(y,z)$. We invite the reader to elaborate these details.

**Definition** A subset $A$ of HF is *$\Delta_1$-definable* if it is both $\Sigma_1$-definable and $\Pi_1$-definable.

In fact there is a whole hierarchy of Sigma, Pi, and Delta definability called the arithmetical hierarchy, but we don't need to pursue this any further.

**Example** Let $E$ be the set of even natural numbers. Then $E$ is a $\Delta_1$-definable subset of HF. To see this, first we have already said that the property of being a natural number is $\Delta_0$-definable in HF. Then $E$ is $\Sigma_1$-definable since $n\in E$ iff there exists an equivalence relation on $n$ such that every class has cardinality $2$. Furthermore the set of odd natural numbers $O$ is $\Sigma_1$-definable using a similar technique. It follows using complements that $E$ is $\Pi_1$-definable, and therefore $\Delta_1$-definable.

Like the $\Delta_0$-formulas, the $\Delta_1$-definable formulas enjoy a degree of absoluteness.

**Proposition** Let $A,B$ be transitive sets and $A\subset B$. If $\phi$ is a $\Sigma_1$ sentence and $A\models\phi$ then $B\models\phi$. If $\phi$ is a $\Pi_1$ sentence and $B\models\phi$ then $A\models\phi$. If $\phi$ is $\Sigma_1$, $\psi$ is $\Pi_1$, and both $A,B$ satisfy $\phi\leftrightarrow\psi$, then $\phi,\psi$ are absolute between $A$ and $B$.

We invite the reader to complete the details of this proposition.

Like the $\Delta_0$-definable sets, the $\Delta_1$-definable sets are decidable in the informal sense, but using the following more complex procedure. Suppose that $A$ is defined both by $\exists y\alpha$ and by $\forall y\beta$, where $\alpha,\beta$ are $\Delta_0$-formulas. The second definition means that $A^c$ is defined by $\exists y\neg\beta$. Our procedure takes an input element $a\in HF$, and runs through all possible values of $b$. Each time it uses the procedure for $\Delta_0$-formulas to check whether $HF\models\alpha[x\mapsto a,y\mapsto b]$ and whether $HF\models\neg\beta[x\mapsto a,y\mapsto b]$. Since $A$ and $A^c$ are complementary, one of these possibilities must eventually be true, at which point we can halt and output Yes or No depending on whether it was $\alpha$ or $\neg\beta$. Note that this procedure will have to terminate, but our description provides no insight as to when it will do so.

Conversely, if a set $A$ is decidable by some procedure, then $A$ should be $\Delta_1$-definable. To see this, we observe that any run of the procedure should leave a finite record of its steps and its state at every step. Such a record can be coded as an element of HF. Thus we can say that $a\in A$ iff there exists a code for a run of the procedure such that the input was $a$ and the output was Yes. And we can say that $a\in A$ iff for all codes for a run of the procedure, if the input was $a$, then the output was Yes.

This informal argument leads to the following historical statement.

**Church–Turing Thesis** A set is decidable by a finitary procedure if and only if it is $\Delta_1$-definable.

In other words, all "reasonable" notions of a finitary procedure should be equivalent to one another. The list of equivalent notions is long and includes: decidable by a Turing machine, decidable by a python program, definable by recursion, and $\Delta_1$-definability. Since all these choices lead to the same concept, the notion of decidable must be very important!

For this class we make the thesis into our formal definition:

**Definition** A subset $A$ of HF is *decidable* if it is $\Delta_1$-definable.

We close with the following useful properties of the class of decidable sets.

**Proposition** The decidable sets of HF are closed under boolean operations and bounded quantification.

*Proof*: It suffices to show that $\Delta_1$-definitions are closed under negation, conjunction, disjunction, and bounded quantification.

Complementation is clear because $\Sigma_1$ and $\Pi_1$ are dual to one another. For disjuctions observe that $\exists x\alpha(x)\wedge\exists x\beta(x)$ is equivalent to $\exists x\exists y\alpha(x)\wedge\beta(y)$, and similarly for $\forall$. Yet another similar argument holds for conjuctions.

For bounded quantification, we will show that $\Sigma_1$ is closed under bounded quantification. The argument for $\Pi_1$ is similar, and the fact for $\Delta_1$ follows. For this, first observe that $\exists x\in y\exists z\alpha$ is equivalent to $\exists z\exists x\in y\alpha$ which is clearly $\Sigma_1$. Next we claim that $\forall x\in y\exists z\alpha$ is equivalent to $\exists u\forall x\in y\exists z\in u\alpha$. The backward implication is trivial. For the forward implication we create a set $u$ which contains a witness $z_x$ for all possible $x\in y$. $\blacksquare$

### 9. Computable functions, recursion, and undecidable sets

In the previous section we introduced decidability for sets. The next logical step is to study functions.

**Definition** A function $f\colon HF\to HF$ is *computable* if and only if it is decidable, that is, $\Delta_1$-definable when considered as a set of pairs.

In practice the terms decidable and computable are often interchanged, but we will typically say decidable when speaking of sets, and computable when speaking of functions. Both terms are correct.

This may lead one to ask whether studying computable functions is any different from studying decidable sets. The following shows computable functions are a nice special case.

**Proposition** If $f$ is a $\Sigma_1$ definable function with domain HF, then $f$ is computable.

*Proof*: Suppose $f$ is $\Sigma_1$ definable. Then there exists a $\Delta_0$-formula $\alpha$ such that $f(a)=b$ iff $HF\models(\exists z)\alpha[x\mapsto a,y\mapsto b]$. Then using the property that on any input $a$, a function always has a unique output $b$, we also have $f(a)=b$ iff $HF\models(\forall y)(\forall z)\alpha(x,y,z)\to y=w[x\mapsto a,w\mapsto b]$. $\blacksquare$

We have studied the informal statement that the decidable sets are those $A$ such that there exists a procedure which on input $a$ decides whether $a\in A$. We now make the informal statement that the computable functions are those $f$ such that there exists a procedure which on input $a$ outputs $f(a)$.

To see this equivalence, first suppose $f$ is computable. Then we can create a procedure which, on input $a$ (in the domain of $f$), searches through all possible values $b$ and uses the $\Delta_1$-definability of $f$ to test whether $(a,b)\in f$. Since $f$ is a function, we know that such a $b$ will eventually be found, upon which the procedure halts with output $b$.

Conversely, suppose there is a procedure for evaluating $f(a)$. Then $f$ is $\Sigma_1$ because $(a,b)\in f$ if and only if there exists a code for a run of the procedure such that the input is $a$ and the output is $b$. Since any $\Sigma_1$ function is automatically $\Delta_1$, we conclude $f$ is computable.

**Example** Suppose $A$ is a decidable set. Then the *characteristic function* $\chi_A$ of $A$ is a computable function. Indeed $(x,i)\in\chi_A$ if and only if $i=1$ and $x\in A$ or else $i=0$ and $x\notin A$. This statement is a boolean combination of $\Delta_1$-formulas.

We invite the reader to check that the converse is true, that is, if some characteristic function $\chi_A$ is computable then $A$ is decidable.

**Example** Let $f$ be the cardinality function $f(x)=\vert x\vert$. Then $f$ is $\Delta_1$ and so computable. Indeed, $f$ is $\Sigma_1$ because $\vert x\vert=y$ iff $y\in\omega$ and there exists a bijection between $x$ and $y$, and $f$ is $\Pi_1$ because $\vert x\vert=y$ iff $y\in\omega$ and every injection from $x$ to $y$ is a surjection.

More substantial examples of computable functions are usually defined by recursion. For instance, we have seen how $+$ can be defined by iteratively adding $1$, and $\times$ can be defined by iteratively adding. The classical recursion theorem is a consequence of ZFC which states that these functions exist. The recursion theorem in computability theory says that if the recursive definition is computable, then the result is computable too.

There are many different ways to state the recursion theorem. Here we present only the simplest version in detail.

**Theorem** If $G\colon\mathbb N^{<\omega}\to\mathbb N$ is computable, then there exists a computable function $F\colon\mathbb N\to\mathbb N$ such that $F(n)=G(F\restriction n)$.

*Proof idea*: In the classical recursion theorem, we prove $F$ exists using the Separation axiom: $F$ is the set of pairs $(n,m)$ such that there exists a natural number $N$ and a function $f$ with domain $N$ such that $f(i)=G(f\restriction i)$ for all $i<N$ and $f(n)=m$. One checks that this defines a function whose domain is all of $\mathbb N$. Moreover $F$ is unique.

Now we observe that the definition given above is in fact a $\Sigma_1$ definition. Since any $\Sigma_1$ function is $\Delta_1$, we conclude that $F$ is computable. $\blacksquare$

In order to define $+$ and $\times$, one would actually need an analogous result for defining $F(m,n)$ in terms of its earlier values $F(i,n)$, $i<m$ and $F(m,j)$, $j<n$. The details are not fundamentally more difficult.

There is also a version of the recursion theorem along $\in$, which allows one to construct functions on HF by defining $F(x)$ in terms of $F(y)$ for all $y\in x$. Thus for example the *rank function* on HF is defined using the recursion $\mathrm{rk}(x)=\max_{y\in x}\mathrm{rk}(y)+1$.

Lastly, there is also a version of the recursion theorem along well-formed formulas. Here we regard well-formed formulas as elements of HF. To do this we can fix numerical codes for every logical symbol and for any finite signature $\mathcal L$. We code an expression by an ordered tuple of codes for symbols.

Let $W\subset HF$ consisting of just the codes for the well-formed formulas. Then $W$ is decidable using a version of the recursion theorem.

Next let $S$ (for "satisfaction") consist al all ordered pairs $(p,s)$ where $p$ is a code for a $\Delta_0$-formula $\phi$, $s$ is a substitution of the free variables of $\phi$, and $HF\models\phi[s]$. Then $S$ is once again decidable using a version of the recursion theorem. Here we are constructing a function $F$ from such pairs $(p,s)$ to $\lbrace T,F\rbrace$ (coded as $\lbrace1,0\rbrace$) in terms of the sub-formulas of $p$ by formalising the definition of $\models$.

#### Undecidable sets

We have now given much thought to what is decidable, and what is computable, and how to construct decidable sets and computable functions. What kinds of sets are not decidable? We first begin with the following.

**Theorem** There exists a set which is $\Sigma_1$-definable but not $\Delta_1$-definable.

This of course justifies giving different names to $\Delta_1$ and $\Sigma_1$ in the first place. To prove it, we will first show that there is a $\Sigma_1$-definable set which is *universal* in the sense that all other $\Sigma_1$-definable sets can be obtained from that one. We will then prove that a universal $\Sigma_1$-definable set cannot be $\Delta_1$-definable.

**Lemma** There exists a $\Sigma_1$-definable set $U\subset HF\times HF$ such that for every $\Sigma_1$-definable set $A\subset HF$ there exists $r\in HF$ such that $A=\set{a:(r,a)\in U}$.

*Proof of Lemma*: Let $V$ be the set of all triples $(p,a,b)$ such that $p$ is a code for a $\Delta_0$-formula $\phi$ and $HF\models\phi[x\mapsto a,y\mapsto b]$. Then we have argued using recursion that $V$ is $\Delta_1$-definable. Next let $U$ be the set of all pairs $(p,a)$ such that $(\exists b)(p,a,b)\in V$. Then $U$ is clearly $\Sigma_1$-definable.

Now if $A$ is any $\Sigma_1$-definable set, then $A$ is definable by some formula $\exists y\phi$ where $\phi$ is a $\Delta_0$-formula. Letting $p$ be a code for $\phi$, we have that $A$ is precisely equal to $\set{a:(p,a)\in U}$, as desired. $\blacksquare$

Intuitively, we can think of $U$ as a $2$-dimensional set where the $\Sigma_1$-definable sets make up the columns of $U$.

To prove the theorem, we once again return to the diagonalization idea of Cantor and Russell.

*Proof of Theorem*. Let $U$ be the universal $\Sigma_1$ set constructed in the Lemma. Let $D=\set{a\in HF:(a,a)\notin U}$. Then the definition of $D$ is clearly $\Pi_1$-definable, due to the negation and the $U$. On the other hand, due to its definition, $D$ cannot not appear as a column of $U$. Since all the $\Sigma_1$-definable sets appear as columns of $U$, we must conclude that $D$ is not $\Sigma_1$-definable.

Letting $A=HF\setminus D$, we have that $A$ is $\Sigma_1$-definable and not $\Pi_1$-definable. In particular, $A$ is $\Sigma_1$-definable but not $\Delta_1$-definable, as desired. $\blacksquare$

While a universal set is usually the first place one would look for an example of an undecidable set, it is not very natural in the sense that it would not arise in practice. We next conclude this section with one of the most famous and naturally occuring examples of an undecidable set.

In the following result, fix any model of computation you prefer, and fix some way of coding procedures in that model as elements of HF. For example if you like python programs, you can code the python commands and symbols as natural numbers, and code a python program as a tuple of natural numbers. For this discussion assume the input is not used (or is the empty set). Then some python programs halt, and others run on forever. We let $H\subset HF$ consist of the set of codes for python programs that halt.

**Theorem** The set $H$ of codes for halting programs is undecidable.

*Proof*: Let $A$ be a $\Sigma_1$ set which is not $\Delta_1$. Let $\phi$ be a $\Delta_0$-formula such that $a\in A$ iff $\exists y\phi(x,y)[x\mapsto a,y\mapsto b]$. For each $a$ let $h_a$ be a code for the program which searches through all possible $b\in HF$ until it finds one such that $HF\models\phi(a,b)$. Then the function $a\mapsto h_a$ is computable, since we can write general such program $h_x$, and given any $a$, subsitute $a$ for $x$ in the program code. Now we have $a\in A$ iff $h_a\in H$. Thus if $H$ were $\Delta_1$ then so would $A$ be $\Delta_1$, a contradicton. $\blacksquare$

In this proof, we defined a function $r\colon HF\to HF$ with the property that $a\in A\iff a(x)\in H$. Such a funcion is called a *reduction* from $A$ to $H$. When there exists a computable reduction from $A$ to $B$ we sometimes write $A\leq B$ because it says in some sense that the complexity of $B$ is no simpler than that of $A$. In general, if one wishes to prove that a given set $B$ is undecidable, the most common technique is to find a computable reduction function from some known undecidable set $A$ to $B$.

### 10. Decidability in logic and incompleteness

In this section we apply our understanding of diagonalization and undecidability in the setting of theories and deductions. The result will be Godel's incompleteness theorems.

We have said that if $\phi$ is a well-formed formula we can view it as an element of HF using any standard coding method. Thus if $T$ is a theory, we can view it as a subset of HF, and ask whether $T$ is decidable or not. Most of the theories that we have discussed in this course are decidable theories, because we listed the axioms in a straightforward way. But exceptions may occur when we use indirect constructions to define $T$, such as $T=\mathrm{Th}(\mathcal A)$ or $T=\bar {T_0}$. Another indirect construction is the following:

**Definition** For any theory $T$ we let $T^\vdash=\set{\sigma:T\vdash\sigma}$. We say $T^\vdash$ is the *deductive closure* of $T$.

If $T$ is decidable, we can still consider the question of whether $T^\vdash$ is decidable or not. We will always have that $T^\vdash$ is $\Sigma_1$, because $\sigma\in T^\vdash$ iff there exists a code for a deduction from $T$ of $\sigma$. We invite the reader to carry out the details of this justification.

For example, ZFC is a decidable theory. Most of the axioms of ZFC are specific well-formed sentences. The Separation and Replacement axioms are actually axiom schemes, which say that for any formula $\phi$ a certain sentence involving $\phi$ is true. Nevertheless these axiom schemes are templates that are easy to recognise. That is, given a sentence $\sigma$, we can imagine a simple condition or procedure to decide whether $\sigma$ is an instance of the Separation or Replacement axiom or not.

But it is much more difficult to decide whether $\sigma$ is in $\mathrm{ZFC}^\vdash$ (that is, $\sigma$ is a *theorem* of ZFC), because this appears to require an unbounded search over all possible deductions. We will see that $\mathrm{ZFC}^\vdash$ turns out to be *undecidable*. Whether that's surprising or not depends on your point of view. ZFC is powerful enough to settle many if not most open problems in mathematics. Thus if $\mathrm{ZFC}^\vdash$ were decidable, then contemporary and future humans and automated theorem provers should be able to settle most open problems in mathematics.

Of course you may feel that studying ZFC is rather specific, since we could always debate, add, and subtract some of the axioms. In the rest of the section, it will be sufficient to work with the following theory which is much more basic.

**Definition** The theory CST, or *core set theory*, consists of Extensionality, Pairing, Union, Separation, and Foundation.

This theory is weak compared with ZFC, particularly because it doesn't imply the existence of infinite sets. CST is strong enough to do finite set theory, including many properties of HF and natural numbers, including induction. It has a similar strength to Peano Arithmetic, the usual axioms of the natural numbers with $+,\cdot$.

**Theorem** (First incompleteness theorem) If $T$ is any consistent extension of CST, then $T^\vdash$ is undecidable.

In our proof of the first incompleteness theorem, we will use a diagonalization argument similar to that used in Russell's paradox, Cantor's uncountability theorem, and the undecidability of the halting problem.

We begin by showing we can "represent" subsets of HF inside the theory $CST$ itself.

**Proposition** Every element of HF is $\Delta_0$-definable. That is, for all $a\in HF$ there exists a $\Delta_0$-formula $\delta_a(x)$ such that $b=a$ iff $HF\models\delta_a(x)[x\mapsto b]$.

The propostion says that in logical formulas, we can reference every single element of HF without needing to expand the signature or theory CST with new constant symbols. It's similar to the situation in arithmetic where we can refer to $n\in\mathrm N$ as the $n$-th least element. We invite the reader to carry out the proof of the result.

**Definition** Let $\mathcal L=\lbrace\in\rbrace$ and $T$ be an $\mathcal L$-theory. Given a formula $\phi(x)$, and an element $a\in HF$, we will say that $T\vdash\phi(\langle a\rangle)$ if and only if $T\vdash\exists x\delta_a(x)\wedge\phi(x)$.

**Definition** With $T$ as above, a subset $A\subset HF$ is *representable* in $T$ if there is a formula $\phi$ such that $a\in A$ if and only if $T\vdash\phi(\langle a\rangle)$.

**Proposition** Let $T$ be a consistent extension of CST. Then every $\Delta_0$-definable set is representable in $T$.

*Proof*: We will prove that for any $\Delta_0$-formula $\phi(x)$, we have $CST\vdash\phi(\langle a\rangle)$ if and only if $HF\models\phi[x\mapsto a]$. For atomic and negated atomic formulas $x\in y$, $x\notin y$, $x=y$, and $x\neq y$ are proved by induction on the rank of the elements $a,b$ that are plugged in for $x,y$. For general $\Delta_0$-formulas $\phi$ we use induction on the complexity of $\phi$. The boundedness of quantifiers is key because they reduce to conjuctions or disjunctions of atomics. $\blacksquare$

Note that the equivalence $CST\vdash\sigma$ if and only if $HF\models\sigma$ is not true in general! For example, let $\sigma$ be the negation of the axiom of Infinity. Then $\sigma$ is true in HF, but CST has models of $\sigma$ and of $\neg\sigma$, so $\sigma$ is not provable from CST.

**Proposition** Let $T$ be a consistent extension of CST. Then every $\Delta_1$-definable set is representable in $T$.

*Proof*: Let $A$ be a $\Delta_1$-definable subset of HF, and let $\alpha,\beta$ be $\Delta_0$-formulas such that $a\in A$ iff $HF\models\exists y\alpha[x\mapsto a]$, and $a\in A$ iff $HF\models\forall z\beta[x\mapsto a]$.

Note that we cannot directly use either of the two formulas $\alpha,\beta$ to represent $A$, because they may be consequences of $T$ without being witnessed in HF. (Another way to think of this is that they may be witnessed by nonstandard elements.) Instead we let $\psi(x)$ be the formula:

$$\exists y\left[\alpha(x,y)\wedge\forall z((\mathrm{rk}(z)<\mathrm{rk}(y))\rightarrow\beta(x,z))\right].$$

We claim that $a\in A$ iff $T\vdash\psi(\langle a\rangle)$. First assume that $a\in A$. Then there is $b\in HF$ such that $HF\models\alpha(x,y)[x\mapsto a,y\mapsto b]$, and for all $c\in HF$ we have $HF\models\beta(x,z)[x\mapsto a,z\mapsto c]$. Since $\alpha,\beta$ are $\Delta_0$, the previous proposition implies $CST\vdash\alpha(\langle a\rangle,\langle b\rangle)$ and $CST\vdash\beta(\langle a\rangle,\langle c\rangle)$. The requirement that $\mathrm{rk}(z)<\mathrm{rk}(y)$ amounts to a finite disjunction over all $c$ of rank less than that of $b$. Thus $CST\vdash\psi(\langle a\rangle)$, and so $T\vdash\psi(\langle a\rangle)$.

Conversely assume that $a\notin A$. We claim that $CST\vdash\neg\psi(\langle a\rangle)$, that is:

$$\forall y\left[\neg\alpha(\langle a\rangle,y)\vee\exists z((\mathrm{rk}(z)<\mathrm{rk}(y))\wedge\neg\beta(\langle a\rangle,z))\right].$$

For this, first find $c\in HF$ such that $CST\vdash\neg\beta(\langle a\rangle,\langle c\rangle)$. Next for any $y$, if $y=b\in HF$ then the first clause holds for $y$, and if not then the second clause holds with $z=c$. Now since $T$ is a consistent extension of CST, we conclude $T\not\vdash\psi(\langle a\rangle)$. $\blacksquare$

We are now ready to prove the final step of the first incompleteness theorem.

**Theorem** Suppose $T$ is a theory such that every $\Delta_1$-definable subset of HF is representable in $T$. Then $T^\vdash$ is undecidable.

*Proof*: Assume $T^\vdash$ is decidable and consider the set:

$$U=\set{(p,a):p\text{ is a code for a formula }\phi\text{ and }T\vdash\phi(\langle a\rangle)}.$$

Then $U$ is decidable, and since every $\Delta_1$-definable set is representable in $T$, every $\Delta_1$-definable set appears as a column of $U$. We say that $U$ is universal for $\Delta_1$-definable sets. Let $D$ be the diagonal set:

$$D=\set{p:(p,p)\notin U}$$

Then due to its definition, $D$ cannot appear as a column of $U$. But  $D$ is also decidable, i.e., $D$ is $\Delta_1$-definable, and so it must appear as a column of $U$. This is a contradiction! $\blacksquare$

The last two results together complete the proof of the first incompleteness theorem. We can also rephrase the first incompleteness theorem as follows.

**Corollary** If $T$ is any consistent, decidable extension of CST then $T^\vdash$ is incomplete.

*Proof*: Since $T$ is decidable, $T^\vdash$ is $\Sigma_1$-definable, because $\sigma\in T^\vdash$ iff there exists a deduction etc. If $T^\vdash$ is complete, we have $T\vdash\sigma$ iff $T\not\vdash\neg\sigma$, which shows $T^\vdash$ is $\Pi_1$-definable as well. It follows that $T^\vdash$ is decidable, but this contradicts the first incompleteness theorem. $\blacksquare$

The corollary is rather stunning, since it implies mathematicians and humanity will never know all the theorems about sets, about arithmetic or about mathematics generally. We can't simply add axioms to ZFC (such as CH etc) to obtain a decidable collection of axioms that is strong enough to prove or disprove everything.

#### The second incompleteness theorem

The corollary to the first incompleteness theorem provides conditions under which there exists a sentence that is neither provable nor disprovable from $T$. However it does not provide an example of such a sentence $\sigma$. The second incompleteness theorem helps give an explicit and relevant example of such a sentence $\sigma$ which concerns the consistency of the theory $T$ itself.

Note that we haven't yet said whether ZFC is consistent or not. We said it is an excellent foundation of mathematics, and we said it has the necessary limitation that *if* it is consistent, then the set of ZFC-theorems is undecidable. But is it consistent?

Maybe we can prove that ZFC is consistent. In fact for any theory $T$ which is decidable, $T$ is coded as a $\Delta_1$-definable subset of HF, and it is possible to construct a sentence $\mathrm{con}_T$ which asserts that there does not exist a deduction from $T$ of $\alpha\wedge\neg\alpha$. Then $\mathrm{con}_T$ asserts that $T$ is consistent.

**Theorem** (Second incompleteness theorem) If $T$ is any consistent, decidable extension of CST, and $\mathrm{con}_T$ is the sentence which asserts that $T$ is consistent, then $T\mathbin{\not\vdash}\mathrm{con}_T$.

The theorem thus implies that if ZFC is consistent, it is not possible for ZFC to prove the sentence $\mathrm{con}_{ZFC}$. We can consider proving $\mathrm{con}_{ZFC}$ from some stronger theory $ZFC^+$, but this theory would not be able to prove $\mathrm{con}_{ZFC^+}$. Essentially, we will have to accept that we can never satisfyingly prove that our foundational theory is consistent. Even though we have used ZFC as a foundation for 100 years without encountering a contradiction, one may yet be found!

The key to the proof of the second incompleteness theorem is once again a diagonalisation lemma.

**Lemma** There exists a "diagonal" sentence $\gamma$ which asserts that "there does not exist a deduction from $T$ of $\gamma$".

That is, $\gamma$ says in a self-referential way, "this sentence is not provable". It is similar the so-called liar paradox sentence, "this sentence is false", but with truth replaced by provability. Truth is usually not definable, but provability is definable using deductions.

*Proof sketch of lemma*: We will be a little bit informal here, but give the general idea. Let $\sigma(p,x)$ be a formula which says "$p$ is a code for a formula $\phi$, and there exists a deduction from $T$ of $\phi(x)$".

Let $\psi(x)$ be the formula $\neg\sigma(x,x)$, so like in the diagonal arguments, $\psi$ does not appear as a "column" of $\sigma$. Then we have:

$$\begin{aligned}
  \psi(\langle\psi\rangle)
  &\iff\neg\sigma(\langle\psi\rangle,\langle\psi\rangle)\\
  &\iff\text{there does not exist a deduction from $T$ of $\psi(\langle\psi\rangle)$}.
\end{aligned}$$

Letting $\gamma$ be $\psi(\langle\psi\rangle)$, we have $\gamma$ is as desired. $\blacksquare$

Due to its contrary nature, it should not be hard to believe that $\gamma$ is correct about itself. That is, so long as $T$ is consistent, we have $T\not\vdash\gamma$. To see this, if $T\vdash\gamma$ then there exists a deduction from $T$ of $\gamma$. Formalising the deduction in CST, we would have "$T\vdash$ there exists a deduction from $T$ of $\gamma$", and hence $T\vdash\neg\gamma$. (This isn't quite a contradiction, it just means $T$ has to be inconsistent in this case.)

*Proof of Theorem*: Assume towards a contradiction that $T\vdash\mathrm{con}_T$. Let $\gamma$ be the diagonal sentence from the lemma.

We have seen that if $T$ is consistent, then $T\not\vdash\gamma$. Formalising this conditional in CST, we have that $T\vdash\mathrm{con}_T\rightarrow$ "there does not exist a deduction from $T$ of $\gamma$". But this says precisely that $T\vdash\mathrm{con}_T\rightarrow\gamma$.

Since we are assuming $T\vdash\mathrm{con}_T$, we can conclude $T\vdash\gamma$. We have seen this implies $T$ is inconsistent, which contradicts our hypothesis, and completes the proof. $\blacksquare$

<script>
  MathJax = {
    tex: {
      inlineMath: [['$', '$'], ['\\(', '\\)']]
    }
  };
</script>
<script id="MathJax-script" async
    src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js">
</script>
