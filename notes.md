---
fontsize: 11pt
header-includes: |
  \usepackage{mathpazo}
  \usepackage{setspace}\onehalfspacing
  \usepackage{geometry}
  \usepackage{hyperref}
  \def\set#1{{\left\{#1\right\}}}
  \def\abs#1{{\left|#1\right|}}
  \def\lt{<}
---

# MATH0037 Lecture Notes

Samuel Coskey

Based partially upon texts and notes by H Enderton, S Thomas, K Kunen, and more.

## Part I: Introduction to logic and set theory

### Introduction

*Logic* is the area of study that concerns reasoning. It has of course been studied by both philosophers and mathematicians for several millennia.

In this module we will study *mathematical logic*, which has been studied since late 1800s. During that period mathematics itself was rapidly evolving and modernising, and mathematical logic was developed to help provide a rigorous foundation for contemporary mathematics.

Mathematical logic helps us understand what language we can use when discussing mathematics, what makes theorem statements meaningful, and what forms of reasoning are appropriate to use in proofs. It also helps us build and study mathematical structures like groups, rings, graphs, and so on.

The modern field of mathematical logic now consists of three interconnected subfields: first order logic, set theory, and computability theory.

In this module we will focus primarily on first order logic. However we will begin our study with the much simpler propositional logic, along with some elementary set theory to support our studies. We will conclude with an introduction to computability theory and the incompleteness phenomenon.

### 1. Propositional logic

We begin our study of mathematical logic with the relatively simple theory of *propositional logic*. This theory deals with the boolean connectives (P implies Q, and so forth) but excludes quantifiers (for all, there exists).

In the next part we will study first order logic, which adds the quantifiers back in. While that means the material of this section will soon be eclipsed, we include it to help us transition from commonly used logic to true mathematical logic.

We begin by introducing the *language* of propositional logic. Every language has an *alphabet*, or set of symbols we may write. The alphabet of propositional logic includes:

* the boolean connective symbols: $\neg$, $\wedge$, $\vee$, $\rightarrow$, $\leftrightarrow$
* propositional variable symbols: $P_1,P_2,P_3,\ldots$ (or sometimes $P,Q,R,\ldots$, $A,B,C,\ldots$, etc)
* brackets, also called parentheses: '$($', '$)$'

We will see later on that the connective symbols $\vee,\rightarrow,\leftrightarrow$ may all be avoided. Moreover, even the brackets may be avoided if one uses prefix notation instead of infix notation. (That is, if one writes $\mathord{\wedge}PQ$ instead of $(P\wedge Q)$.) For the moment we will continue with the more familiar infix notation.

Next, a language should tell us how to put symbols from the alphabet together.

**Definition** An *expression* is any finite sequence of symbols using the alphabet of propositional logic.

For example, both of the following are expressions:

* $(P\wedge Q)\vee R$
* $((P\rightarrow)$

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

In logic we often separate the *syntax* and the *semantics* of formulas. Syntax is all about rules, you can think of it as analogous to grammar for languages. for example, what is and isn’t considered a well-formed formula, much like grammar. On the other hand, semantics is all about meaning, for example, which formulas might be considered true or false.

The semantics of propositional logic is governed by truth tables. In the following, let $\alpha$ and $\beta$ be well-formed formulas.

$\begin{array}{c|c}\alpha&(\neg\alpha)\\\hline T&F\\F&T\end{array}$

$\begin{array}{cc|c}\alpha&\beta&(\alpha\wedge\beta)\\\hline T&T&T\\T&F&F\\F&T&F\\F&F&F\end{array}$

The boolean connective $\rightarrow$ always sparks a little bit of discussion.

$\begin{array}{cc|c}\alpha&\beta&(\alpha\rightarrow\beta)\\\hline T&T&T\\T&F&F\\F&T&T\\F&F&T\end{array}$

Sometimes called *material conditional*, the truth table is meant to capture the idea of “P implies Q”, but without any of the causation one would normally understand from natural language. Instead the formula $\alpha\rightarrow\beta$ may be thought of as a kind of promise, that if $\alpha$ is true then $\beta$ will be true also. If $\alpha$ is not true, then the promise will not be broken, so the conditional is "vacuously true". We will see later that this definition is the most useful way to study deductions in mathematics.

We invite the reader to fill in truth tables for the rest of the boolean connectives.

While these truth tables are certainly familiar, we still need to describe how they are used. We will say the set of *truth values* is $\set{T,F}$.

**Definition** A *truth assignment* is a function $v$ from the set of propositional symbols to the set of truth values. That is, $v\colon\set{P_1,P_2,\ldots}\to\set{T,F}$.

In other words, a truth assignment $v$ says whether each propositional symbol is true or false. Since the propositional symbols are the simplest well-formed formulas, intuitively we should be able to use $v$ together with the truth tables for the boolean connectives to determine whether $v$ says any well-formed formula $\alpha$ is true or false. The following definition makes this idea formal.

**Definition** Let $v$ be a truth assignment and $\alpha$ be a well-formed formula. We define $v\models\alpha$, read aloud "$v$ satisfies $\alpha$", using the following base case and recursive rules.
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

**Theorem** (The compactness theorem). Let $\Sigma$ be a set of well-formed formulas. If $\Sigma\models\alpha$, then there exists a finite subset $\Sigma_0\subset\Sigma$ such that $\Sigma_0\models\alpha$.

The compactness theorem for propositional logic is one of the cornerstones of the theory, as will be the more general compactness theorem for first order logic. The name of the compactness theorem is due to its relationship to the idea of compactness in analysis, something which will become a little clearer later on.

The compactness theorem can be restated as a statement about consistency.

**Definition** Let $\Sigma$ be a set of well-formed formulas. We say $\Sigma$ is *consistent* if there exists a truth assignment $v$ such that $v\models\Sigma$.

We invite the reader to verify that $\Sigma$ is consistent if and only if $\Sigma\not\models (P\wedge(\neg P))$. Sometimes the symbol $\bot$ is used for a tautologically false formula such as $(P\wedge(\neg P))$. Thus we may say $\Sigma$ is consistent if and only if $\Sigma\not\models\bot$.

**Theorem** (The compactness theorem again). Let $\Sigma$ be a set of well-formed formulas. If every finite subset of $\Sigma$ is consistent, then $\Sigma$ is consistent.

We leave it to the reader to establish an equivalence between the two statements of the compactness theorem.

The compactness theorem has many interesting applications, to give a taste of this we explore just one of them from combinatorial graph theory. Recall that if $G=(V,E)$ is a graph with vertex set $V$ and edge set $E$, then a *proper coloring* of $G$ with $n$ colors is a function $\chi\colon V\to \set{c_1,\ldots,c_n}$ such that whenever $(v,v')\in E$ we have $\chi(v)\neq\chi(v')$.

**Theorem** Let $G$ be a combinatorial graph, finite or infinite. Suppose that every finite subgraph $G_0\subset G$ has a proper coloring using $n$ colors. Then $G$ has a proper coloring using $n$ colors. In particular, every planar graph (finite or infinite) has a proper coloring using $4$ colors.

*Proof*: They key is that proper colorability can be encoded using well-formed formulas. For convenience we will use the propositional variable symbols $P_{v,i}$, where $v$ ranges over the vertices $V$ and $i\in 1,\ldots,n$. We then let $\Sigma$ consist of the following axioms:

* $P_{v,1}\vee\cdots\vee P_{v,n}$ for each $v\in V$ and each $i$
* $\neg(P_{v,i}\wedge P_{v,j})$ for each $v\in V$ and each $i.j$ such that $i\neq j$
* $\neg(P_{v,i}\wedge P_{w,i})$ for each $v,w\in V$ such that $(v,w)\in E$ and each $i$

The reader should verify that there exists a truth assignment $v$ that satisfies $\Sigma$ if and only if there exists a proper coloring $\chi$ using $n$ colors.

We claim $\Sigma$ is finitely satisfiable. To see this let $\Sigma_0\subset\Sigma$ be a finite subset. Note that since $\Sigma_0$ is finite and each sentence is finite in length, there exists a finite susbest $V_0\subset V$ of vertices appearing in the subscript of a propositional symbol in $\Sigma_0$. If we let $G_0$ be the subgraph of $G$ induced by $V_0$, then by hypothesis there exists a proper coloring $\chi_0$ of $G_0$ using $n$ colors. As observed in the previous paragraph, this implies that $\Sigma_0$ is consistent.

Therefore by the compactness theorem, $\Sigma$ is satisfiable. Again, as we have seen, this implies there exists a proper coloring of $G$ using $n$ colors. $\blacksquare$

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

1. $(\neg S)\vee R$ — (hypothesis)
2. $((\neg S)\vee R)\rightarrow (S\rightarrow R)$ — (tautology)
3. $S\to R$ — (modus ponens)
4. $S$ — (hypothesis)
5. $R$ (modus ponens)
6. $R\rightarrow P$ (hypothesis)
7. $P$ (modus ponens)

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

We invite the reader to check that this construction "works" in the sense that two ordered pairs are equal if and only if their left and right components are equal. One should observe that many simpler attempts don't work, such as $\set{\{a\},\{b\}}$ or $\set{a,\set{a,b}}$.

**Definition** Let $A,B$ be sets. The *cartesian product* of $A$ and $B$ is defined as $A\times B=\set{(a,b):a\in A,\ b\in B}$.

For instance, $\mathbb R\times\mathbb R$ is the Cartesian plane, and $\mathbb Z\times\mathbb Z$ is the grid points of the Cartesian plane.

**Definition** Let $A,B$ be sets.
* A *binary relation* between $A$ and $B$ is any subset $R\subset A\times B$. We sometimes write $aRb$ to mean that $(a,b)\in R$.
* The *domain* of $R$ is $\set{a\in A:(\exists b)(a,b)\in R}$
* The *range* of $R$ is $\set{b\in B:(\exists a)(a,b)\in R}$

For example, the $<$ relation on real numbers is a binary relation between $\mathbb R$ and itself. Formally, $<$ is the set of all pairs $(m,n)\in\mathbb R\times\mathbb R$ such that $m$ is less than $n$. Thus $<$ is "physically" a region in the plane.

Functions are special examples of binary relations. In elementary mathematics, we often teach that a function is a formula or rule. But in formal mathematics, a function is "physically" its graph, which is the set of ordered pairs (input, output).

**Definition** Let $A$ and $B$ be sets.
* A *function* from $A$ to $B$ is a binary relation $f\subset A\times B$ with the property: for all $a\in A$ there exists a unique $b\in B$ such that $(a,b)\in f$.
* $f$ is *injective* or *one-to-one* if $(a,b),(a',b)\in f$ implies $a=a'$
* $f$ is *surjective onto* $B$ (or simply *surjective* when $B$ is clear from context) if the range of $f$ is equal to $B$.
* $f$ is *bijective* between $A$ and $B$ if it is injective and surjective onto $B$.

When $f$ is a function from $A$ to $B$ we may write $f\colon A\to B$, and when $(a,b)\in f$ we may write $f(a)=b$.

**Example** In lectures we will give some examples of functions, their graphs, and their properties.

**Definition** Let $A,B$ be sets. Then $B^A$ denotes the set of functions from $A$ to $B$.

We note that in other resources the set $B^A$ may be written as ${}^AB$ or $\mathrm{Fun}(A,B)$ (because it is fun).

#### Rooted trees and Konig's lemma

In combinatorics a tree is a special kind of combinatorial graph, one without cycles. In set theory we view trees slightly differently, with a root vertex and other vertices labeled by elements of a set $X$. Here we introduce the set-theoretic terminology and notation surrounding trees.

**Defintion**. Let $X$ be any set.
* The *full tree* on $X$, denoted $X^{<\mathbb N}$ is the set of all functions $t$ whose domain is an initial segment of $\mathbb N$ and whose range is contained in $X$, that is, $t\colon\set{0,\ldots,n-1}\to X$ for some $n\in\mathbb N$.
* The $n$th *level* of $X^{<\mathbb N}$ is the set of all $t$ of length $n$, that is, $|t|=n$.
* If $s,t\in X^{<\mathbb N}$, we say $s$ is a *predecessor* of $t$, or $t$ is a *successor* of $s$, if $s\subset t$.
* $t$ is an *immediate successor* of $s$ if $t$ is a successor of $s$ and $|t|=|s|+1$.

**Definition** Let $X$ be any set. A *tree* on $X$ is a subset $T\subset X^{<\mathbb N}$ of the full tree on $X$ which is closed under predecessors, that is, for all $s,t\in X^{<\mathbb N}$, if $s\subset t\in T$ then $s\in T$.

In lectures we will give several examples of set-theoretic trees.

**Definition** Let $X$ be any set.
* The set of sequences on $X$, denoted $X^{\mathbb N}$ is the set of all functions $f\colon\mathbb N\to X$.
* For any sequence $f\in X^{\mathbb N}$ and any $n\in\mathbb N$ the *restriction* of $f$ to $n$, denoted $f\restriction n$, is the initial segment of $f$ with domain $\set{0,\ldots,n-1}$.
* Let $T$ be a tree on $X$. A sequence $f\in X^{\mathbb N}$ is a *branch* through $T$ if for all $n\in\mathbb N$ we have $f\restriction n\in T$.

IN lectures we will give several examples of branches through set-theoretic trees.

We now give a fundamental application of the propositional compactness theorem to the study of trees and branches.

**Theorem** (Konig's lemma) Let $T$ be a tree on $X$ such that every level of $T$ is nonempty and finite. Then there exists a branch through $T$.

We invite the reader to give an example of a tree $T$ such that every level of $T$ is nonempty but there are no branches through $T$.

*Proof*: They key is that the existence of a branch can be encoded using well-formed formulas. For convenience we will use the propositional variable symbols $P_t$, where $t$ ranges over the elements of $T$. We then let $\Sigma$ consist of the following axioms:

* $P_{t_1}\vee\cdots\vee P_{t_k}$ where $t_1,\ldots,t_k$ is the list of elements of $T$ of length $n$, for each $n$
* $\neg(P_{t_i}\wedge P_{t_j})$ where $t_1,\ldots,t_k$ is the list of elements of $T$ of length $n$, for each $n$ and each $i\neq j$
* $P_t\rightarrow P_s$ where $s,t\in T$ and $s\subset t$

The reader should verify that there exists a truth assignment $v$ that satisfies $\Sigma$ if and only if there exists a branch through $T$.

We claim $\Sigma$ is finitely satisfiable. Let $\Sigma_0\subset\Sigma$ be a finite subset, and note that there exists a maximum level $n\in\mathbb N$ which is the length of an element appearing in the subscript of a propositional symbol in $\Sigma_0$. Since $T$ is infinite, $T$ certainly contains a partial branch up to level $n$, and this implies that $\Sigma_0$ is consistent.

Therefore by the compactness theorem, $\Sigma$ is consistent. This implies there exists a branch through $T$. $\blacksquare$

Konig's lemma has many important applications, we present just one. We first recall that the set $X^{\mathbb N}$ is a metric space, where two sequences are close together if they agree on a long partial sequence. Formally we let $d(f,g)=1/N$, where $N$ is the maximum number such that $f\restriction N=g\restriction N$. Thus a sequence of elements $f_n\in X^{\mathbb N}$ converges to $f\in X^{\mathbb N}$ if the length of agreement between $f_n$ and $f$ goes to infinity.

**Theorem** Let $2=\{0,1\}$. The metric space $2^{\mathbb N}$ is compact.

*Proof*: Let $f_n\in 2^{\mathbb N}$. We wish to show that there exists a subsequence $f_{n_k}$ which converges to some $f\in 2^{\mathbb N}$ in the sense of the metric described above.

Copy lars use Konig's lemma or leave as an exercise with hints

$\blacksquare$

**Theorem** (Compactness theorem) Let $\Sigma$ be a set of well-formed formulas such that every finite subset of $\Sigma$ is consistent. Then $\Sigma$ is consistent.

*Proof*: We observe that if we identify $\{T,F\}$ with $\{0,1\}$, then the set of truth assignments $v$ is equivalent to the set $2^{\mathbb N}$, and therefore has the metric described above.

We invite the reader to verify that if $\alpha$ is any well-formed formula, then the set $V_\alpha$ of all truth assignments $v$ such that $v\models\alpha$ is a closed subset of $2^{\mathbb N}$. By the same argument, if $A$ is any finite set of well-formed formulas, then the set $V_A$ of all truth assignments $v$ such taht $v\models A$ is a closed subset of $2^{\mathbb N}$.

We further recall the following fact from analysis. Let $X$ be a compact metric space, and let $\mathcal F$ be a family of closed subsets of $X$. If for all $A_1,\ldots A_n\in\mathcal F$ we have $A_1\cap\cdots\cap A_n\neq\emptyset$, then $\bigcap\mathcal F\neq\emptyset$. (Indeed this may be taken as the definition of a compact metric space.)

Now let $\Sigma$ be a set of well-formed formulas such that every finite subset of $\Sigma$ is consistent. Let $\mathcal F$ be the family of all $V_A$ where $A$ is a finite subset of $\Sigma$.

We observe that if $V_{A_1},\ldots, V_{A_n}\in\mathcal F$ then $V_{A_1}\cap\cdots\cap V_{A_n}=V_{A_1\cup\cdots\cup A_n}$. Since $A_1\cup\cdots\cup A_n$ is a finite subset of $\Sigma$, it is consistent, and therefore there exists $v$ such that $v\models A_1\cup\cdots\cup A_n$. By definition this implies $v\in V_{A_1}\cap\cdots\cap V_{A_n}$, so $V_{A_1}\cap\cdots\cap V_{A_n}\neq\emptyset$.

It follows from the fact from analysis that there exists $v\in\bigcap\mathcal F$. Again by definition this means that $v\models\Sigma$. Thus, $\Sigma$ is consistent. $\blacksquare$

We remark that the results of this section show that the following three statements are all equivalent:

1. The compactness theorem
2. Konig's lemma
3. The space $2^{\mathbb N}$ is compact

This gives some some explanation of the reason for the name of the compactness theorem. Of course, it is also possible to prove each of the three of these results directly.

We remark that we have only proved the compactness theorem when there are a *countable* number of propositional variable symbols in our language $P_1,P_2,\ldots$. The compactness theorem remains true when there are an uncountable number of propositional symbols, but this result is stronger and the proof is different.

### 3. Set theory as a foundation

We have promised that set theory is somehow the theory of everything, meaning all other objects of mathematical study can be regarded as sets. Perhaps the most important objects in mathematics are natural numbers. How can these be regarded as objects in the universe of sets?

We have talked about how set theory is a foundation for the construction of mathematical objects. But the actual development of set theory used the same ordinary mathematical reasoning as one would use in any other area of mathematics: definitions, theorems, and proofs.

We have said that set theory can be used as a foundation for essentially all of mathematics. So far we have explicitly constructed the natural numbers and alluded to the construction of the real numbers.

In set theory, **everything** is a set, meaning we do not distinguish between sets and elements.

The starting point for set theory is therefore the empty set, denoted $\emptyset$. The empty set has the property that $x\in\emptyset$ is always fales. We leave it to the reader to verify that the empty set is unique.

* Von Neumann ordinals: an ordinal is a counting number (as opposed to a quantity measuring number). Define $0,1,2,3,\ldots$ as particular hereditarily finite sets.
* We have also promised that set theory is somehow the theory of the infinite, meaning we can study different kinds of infinity using sets. The axiom of infinity will allow us to count into the infinite.
* In general, an ordinal is equal to the collection of ordinals that came before it. Thus the Von Neumann ordinals will be extended into the infinite by setting $\omega=\set{0,1,2,3,\ldots}$, $\omega+1=\set{0,1,2,3,\ldots,\omega}$ and so on. Infinity plus one!
* Thus we have a successor function $S(\alpha)$ or $\alpha+1$ is equal to $\alpha\cup\set{\alpha}$. 

* Now we do so more explicitly.
* Def. $\mathbb N=\omega$.
* Def. $\mathbb Q$ is the set of triples $(i,m,n)$ in $2\times\omega\times\omega$ satisfying $n\neq0$ and $\mathrm{gcd}(m,n)=1$.
* Here we intrepret $i=0$ as positivet, $i=1$ as negative, $m$ as the numerator, and $n$ as the denominator.
* Def. $\mathbb Z$ is the subset of $\mathbb Q$ where $n=1$.
* It is an exercise to define the operations $+,\times$ and the $<$ relation on $\mathbb Q$ with this definition. For instance $(0,m,n)\times(0,m',n')=$ the result of canceling common factors from $(0,mm',nn')$.
* Observe that with this definiton we don't have $\mathbb N\subset\mathbb Z$. However we can identify $\mathbb N$ with the subset of $(0,m,1)$. This identification would be cumbersome to write explicitly, but once we agree it can be done in principle, we abuse notation and pretend it is being done behind the scenes.
* So far everything constructed is contained in $V_\omega$.
* Def. $\mathbb R$ is the set of dedekind cuts of $\mathbb Q$. Here $C\subset\mathbb Q$ is a cut if
  * $C\neq\emptyset,\mathbb Q$
  * $C$ is closed downwards
  * $C$ has no last element
* Again one must define the opertaions $+,\times$ and $<$ relation. For instance $C+C'=\set{q+q'\mid q\in C,q'\in C'}$.
* Def. $\mathbb C=\mathbb R\times\mathbb R$.
* Def. $\mathbb R[x]$ is the set $\mathbb R^{<\omega}=\bigcup_n\mathbb R^n$. Each sequence $a_0,\ldots,a_n$ is interpreted as the polynomial $a_0+a_1x+\cdots+a_nx^n$.
* Def. $\mathbb R[[x]]$ is the set $\mathrm{Fun}(\omega,\mathbb R)$. Each sequence $a_0,a_1,\ldots$ is interpreted as the formal series $\sum a_nx^n$.
* There are also algebraic descriptions of these constructions: $\mathbb N$ is a semigroup, $\mathbb Z$ is the group completion of that, $\mathbb Q$ is the field of fractions of that, $\mathbb R$ is the real closure of that, $\mathbb C$ is its algebraic closure of that.
* We can also express logic in set theory! A logical expression is a sequence of logical symbols $\wedge,\vee,\forall,\exists,\ldots$ and variables and non-logical symbols. We can use even numbers $2k$ for variables $x_1,x_2,\ldots$, and use odd numbers for the other symbols. Thus a logical expression is a finite sequence of natural numbers, or element of $\omega^{<\omega}$.
* A proof is sequence of logical expressions, where each one follows from the previous by simple deductive rules. Thus a proof is a finite sequence of elements of $\omega^{<\omega}$, or an element of $()\omega^{<\omega})^{<\omega}$. It is still an element of $V_\omega$!

## Part II: First order logic and completeness

The propositional logic we studied in the previous part is a mathematical language that captures some portion of the reasoning that we do as mathematicians. However the language of boolean connectives leaves out something very important, which is the quantifiers "for all" and "there exists".

In this section we introduce first order logic, which reintroduces these quantifiers. The term "first order" means the quantifiers range over elements of a given universe. "Second order" would mean the quantifiers may range over sets and functions, but we will not study this.

### 4. Syntax and theories



While one can imagine making a wide variety of choices for the language, it is natural to restrict to the "first order" logic we have been using in this course and in ordinary mathematics. We have seen that this language is powerful enough to express almost all mathematical concepts, and we will see that it is simple enough that we can reason and prove thoerems about it.


First order logic has two parts: proof theory and model theory. In proof theory we study what it means to give a correct proof of a statement from a set of given axioms. In model theory we study a given set of axioms and the possible universes where the axioms are true.
* For example, group theory consists of the axioms
  * $(\forall x,y,z)(xy)z=x(yz)$
  * $(\exists u)(\forall x)xu=x\wedge ux=x\wedge(\exists y)xy=u$
* If we let $\phi$ be the sentence $(\forall x,y,z)xy=xz\rightarrow y=z$ then $\phi$ is a theorem of group theory. Proof theory says we can find a proof of $\phi$ from the axioms. Model theory says that $\phi$ is true in every universe of the axioms (group).

Until now we have been fairly informal with logic, mixing the official symbols with english and additional ad-hoc symbols. Now it is time to be perfectly formal.

In the first section we introduced the syntax of propositional logic.

In math we often mix prefix ($\neg P$, $f(x)$, $-3$), infix ($x+y$, $x>y$, $P\rightarrow Q$), and postfix ($n!$, $f'$, $\kappa^+$) notations.

For this part of the module, we officially adopt prefix notation for everything. This helps us reduce ambiguity such as $P\rightarrow Q\rightarrow R$. It also eliminates the need for parentheses.

For example the expression $f(n!,x)>5$ will be written $>f!nx5$. Take a minute to think about that!

In order to read such an expression, the reader will have to know the arity of each symbol, that is, how many inputs the symbol is supposed to eat.

**Definition** An *alphabet* is a set $\Sigma$ of symbols.

**Definition** An *expression* in a given alphabet is a finite sequence of symbols of the alphabet.

* Def. A lexicon consists of an alphabet together with an arity function $a\colon\Sigma\to\omega$.
* Def. An expression is well-formed if it is of the form $s\tau_1\cdots\tau_n$ where $\tau_i$ are well-formed expressions.
* Example. The lexicon for expressing polynomials with coefficients $1--4$ consists of alphabet $\set{1,2,3,4,x,+,\cdot}$ with arity function $a(1),\ldots,a(4),a(x)=0$ and $a(+)=a(\cdot)=2$. Then the expression $+\cdot\cdot xx+\cdot2x1$ is one way to represent the polynomial $3x^2+2x+1$. This begins with $s=+$ and is followed by $\tau_1=\cdot3\times xx$ and $\tau_2=+\cdot2x1$. Each of these may then be further broken down. (There are several other representations due to associativity and commutativity.)
* Example. The expression $+\cdot+\cdot$ is not well-formed.
* We now wish to argue that well-formed expressions can only be parsed or read in one way. That is, there are not different $\tau_i$'s that do the job. This is in contrast to $P\rightarrow Q\rightarrow R$, which needs parentheses, which makes the following harder to state and prove.
* Theorem. Let $\sigma$ be a well-formed expression. (1) No proper initial segment of $\sigma$ is well-formed. (2) If $\sigma$ starts with the symbol $s$ of arity $n$ then there exist unique well-formed expressions $\tau_1,\ldots,\tau_n$ such that $\sigma=s\tau_1\cdots\tau_n$.
* Proof. Assume the theorem is true for all expressions which are shorter than $\sigma$. By definition of well-formed, there exist $\tau_i$ such that $\sigma=s\tau_1\cdots\tau_n$. Let $\sigma'$ be a well-formed initial segment of $\sigma$ (not necessarily proper). Then again there exist $\tau'_i$ such that $\sigma'=s\tau'_1\cdots\tau'_n$. Then $\tau_1=\tau'_1$ since otherwise one would be an initial segment of the other, and contradicting the inductive hypothesis. Similarly $\tau_i=\tau'_i$ for all $i$. Thus $\sigma'=\sigma$ and the $\tau_i$ are unique, establishing both (1) and (2).
* Cor. If $\sigma$ is well-formed, then every symbol of $\sigma$ is the beginning of a unique well-formed subexpression called the scope of the occurrence of the symbol.
* Proof. Assume the theorem is true for expressions shorter than $\sigma$. The first symbol of $\sigma$ has scope $\sigma$. Any other symbol appears in some $\tau_i$ and we can apply the inductive hypothesis.
* Activity: Play around with the statement "there are infinitely many primes". Write it in traditional syntax, prefix, and parse tree.

#### First order syntax

* In the first part of the course, we have used first-order logic and logical notation in a somewhat informal way. That is, we introduced the symbols and said what they mean, but we left it to intuition to express and interpret formulas properly.
* In the previous class, we defined lexicon, prefix notation, and the concept of well-formed expression. We proved that well-formed expressions are not at risk for having multiple interpretations, as well as some other useful facts.
* Now it is time to apply the concept of well-formed expressions to first-order logic, thus finally making the logic a formal system.
* The lexicon of first-order logic consists of the alphabet $\Sigma=\set{\forall,\exists,\wedge,\vee,\rightarrow,\leftrightarrow,=,\neg}\cup\set{x_n\mid n\in\omega}$. The arity function is defined as $a(x_i)=0$, $a(\neg)=1$, and all others are $2$.
* In a given context, we will extend the lexicon to include additional function and relation symbols with given arity. Examples include $+,\cdot,<$.
* Def. A signature $\mathcal L$ of first-order logic consists of function symbols $f_i$ and relation symbols $R_j$ as well as arity values $a(f_i)$ and $a(R_j)$. This is the context described above.
* Def. Given a signature $\mathcal L$, the corresponding first-order lexicon consists of $\mathcal L$ together with the first-order lexicon described above.
* We next wish to define the well-formed formulas of first-order logic. Note that this is not as simple as saying that a well-formed formula is a well-formed expression in the lexicon of first-order logic. While it is true that we want our formulas to be well-formed expressions, there are actually some well-formed expressions that should not be formulas. For example consider the expressions $\forall xy$, or $\forall>xyz$.
* Def. Let $\mathcal L=\set{f_i,R_j}$ be a signature of first-order logic.
  * The *terms* of $\mathcal L$ are the well-formed expressions in the lexicon consisting of just the $f_i$ and $x_n$.
  * The *atomic formulas* of $\mathcal L$ are the expressions of the form (1) $R\tau_1\cdots\tau_n$, where $R$ is an $n$-ary relation symbol and $tau_i$ are terms, or; (2) $=\tau_1\tau_2$ where $\tau_i$ are terms.
  * The *well-formed formulas* of $\mathcal L$ are the expressions of the form (1) an atomic formula; (2) $\forall x\phi$ or $\exists x\phi$ where $x$ is a variable and $\phi$ is a wff; (3) $\neg\phi$ where $\phi$ is a wff, or; (4) $\wedge\phi\psi$, $\vee\phi\psi$, $\rightarrow\phi\psi$, $\leftrightarrow\phi\psi$, where $\phi,\psi$ are wffs.
* Like the definition of well-formed expression, this definition is recursive. But unlike the definition of well-formed expression, we have placed further limitations on precisely which well-formed expressions are legal.
* For example, $\forall x\forall y\wedge=++xy\cdot\cdot zzw\cdot3x>\cdot xy\cdot xz$. Put another way $\forall x\forall y(x+y)+z^2w=3x\wedge xy>xz$. Evaluate which are terms, atomics, and general formulas.
* We are claiming that the well-formed formulas are the expressions that can be given meaning. However there are still a few barriers before we can think of assigning a truth value to a wff.
* First, some wffs have free variables, that is, variables that are never quantified. Consider the statement of real numbers $\forall x x\cdot x\geq y$. This would be true if $y=0$, but it would be false if $y=1$. We can repair this by quantifying the $y$, for example, $\exists y\forall x x\cdot x\geq y$ is true of real numbers.
* Def. If $\phi$ is a wff, an occurrence of $x$ in $\phi$ is said to be *bound* if it lies inside the scope of a $\forall x$, and free otherwise.
* Def. If $\phi$ is a wff, $\phi$ is called a *sentence* if it has no free variables occurring.
* The sentences are the well-formed formulas for which we can conceivable assign a truth value. But we may not be able to yet. For example consider the sentence $\exists y\forall x x\leq y$. This sentence is false of real numbers but true of the unit interval $[0,1]$.
* For another example consider $\forall x x\geq 0\rightarrow \exists y y\cdot y=x$. This is true of real numbers but false of rational numbers.
* In order to decide the truth value of a sentence, we need to be told the context of the variables. The first example above says "the universe has an upper bound," but what is the universe?
* The question of what is the universe leads us to model theory. We have seen that set theory is a foundational theory, which means that essentially all mathematical structures can be built using sets. Given a language $\mathcal L$, we can use set theory to study the special sets that can serve as universes for well-formed formulas of $\mathcal L$.
* If $\mathcal L$ is a language of first-order logic, an $\mathcal L$-structure $\mathcal A$ consists of:
  * A set $A$, the universe of the structure
  * For each $n$-ary function symbol $f$ a function $f^{\mathcal A}\colon A^n\to A$
  * For each $n$-ary relation symbol $R$ a relation $R^{\mathcal A}\subset A^n$
  * For each $0$-ary function symbol $c$ a constant $c^{\mathcal A}\in A$
  * For each $0$-ary relation symbol $P$ a truth value $P^{\mathcal A}\in\set{T,F}$
* For example, all the models in the first week's set theory homework are structures for $\mathcal L=\set{\in}$.
* For example, $(\mathbb Q;<)$ is a structure in the language of linear orders.
* For example, $(\mathbb R;0,1,+,\cdot,<)$ is a structure in the language of ordered fields.
* Thus we will not define whether a given sentence $\sigma$ is true or false in general, but whether it is true or false in a given structure $\mathcal A$. We will say that $\mathcal A$ satisfies $\sigma$, and write $\mathcal A\models\sigma$, when $\sigma$ is true in $\mathcal A$.
* The formal definiton of satisfaction is somewhat involved, but will work the way you want it to! For example, returning to the sentence $\forall x x\geq 0\rightarrow \exists y y\cdot y=x$, we will have that $(\mathbb R;+,\cdot,0,1)\models\sigma$ and $(\mathbb Q;+,\cdot,0,1)\not\models\sigma$.

### 5. Semantics, structures, and satisfaction

In this section we give a formal definition of the satisfaction relation $\mathcal A\models\sigma$. Unsurprisindly, the definition will once again be by induction on the construction of the sentence $\sigma$. Of course all the subformulas of $\phi$ are terms and formulas, not sentences, so we will need to handle the case when formulas $\phi$ have free variables.

However, if $\phi(x)$ has free variable $x$, then the statement $\mathcal A\models\phi(x)$ doesn't make sense because we don't know what $x$ is. We instead define the more complicated statement $\mathcal A\models\phi(x)[x\to a]$.

**Example** Let $\mathcal A$ be the model $(\mathbb N,+,\cdot,0,1)$ and let $\phi(x)$ be the formula $x^2<10$. Then $\mathcal A\models\phi(x)[x\to3]$ and $\mathcal A\not\models\phi(x)[x\to4]$.

We begin our recursive definiton of satisfaction by showing how to evaluate the terms.

**Definition** Let $\mathcal L$ be a language of first-order logic and $\mathcal A$ be an $\mathcal L$-structure. Let $s$ be a set of substitutions $x\to a$ of variables being used by elements of $A$ (in other words, a function from the set of variables being used to $A$). Then:

* If $x$ is a variable of $\tau$, define $\mathop{\mathrm{val}}_{\mathcal A}(x)[s]$ to be $s(x)$
* If $c$ is a constant symbol of $\tau$, define $\mathop{\mathrm{val}}_{\mathcal A}(c)[s]$ to be $c^{\mathcal A}$
* If $f$ is an $n$-ary function symbol and $\tau_1,\ldots,\tau_n$ are terms, define $\mathop{\mathrm{val}}_{\mathcal A}(f\tau_1\cdots\tau_n)[s]=f^{\mathcal A}(\mathop{\mathrm{val}}_{\mathcal A}(\tau_1)[s],\ldots,\mathop{\mathrm{val}}_{\mathcal A}(\tau_n)[s])$.

**Example** Let $\mathcal A$ be the model $(\mathbb N,+,\cdot,0,1)$ and let $\tau$ be the term $x\cdot y$. Let $s$ be the substitution $x\to 3,y\to 4$. Then $\mathop{\mathrm{val}}_{\mathcal A}(\tau)[s]=\mathop{\mathrm{val}}_{\mathcal A}(x)[s]\cdot \mathop{\mathrm{val}}_{\mathcal A}(y)[s]=3\cdot 4=12$.

We next define satisfaction for atomic formulas.

**Definition** Let $\mathcal L$ be a language of first-order logic and $\mathcal A$ be an $\mathcal L$-structure. Let $s$ be a set of substitutions. Then:

* If $\phi$ is the formula $R\tau_1\cdots\tau_n$ then $\mathcal A\models\phi[s]$ is true if and only if $(\mathop{\mathrm{val}}_{\mathcal A}(\tau_1)[s],\ldots,\mathop{\mathrm{val}}_{\mathcal A}(\tau_n)[s])\in R^{\mathcal A}$.
* If $\phi$ is the formula $=\tau_1\tau_2$ then $\mathcal A\models\phi[s]$ is true if and only if $\mathop{\mathrm{val}}_{\mathcal A}(\tau_1)[s]=\mathop{\mathrm{val}}_{\mathcal A}(\tau_2)[s]$
* If $\phi$ is the formula $P$, a propositional relation, then $\mathcal A\models\phi$ is true if and only if $P^{\mathcal A}=T$.

Note that in this definition the equality relation is treated specially. This guarantees that the equality relation always represents true equality, and not some funny model-specific notion of equality.

We finally define satisfaction for general formulas.

**Definition** Let $\mathcal L$ be a language of first-order logic and $\mathcal A$ be an $\mathcal L$-structure. Let $s$ be a set of substitutions. Then:

* If $\phi$ is $\alpha\wedge\beta$ then $\mathcal A\models\phi[s]$ is true if and only if $\mathcal A\models\alpha[s]$ and $\mathcal A\models\beta[s]$
* Similarly use the truth tables for $\wedge,\to,\leftrightarrow$
* If $\phi$ is $\neg\alpha$ then $\mathcal A\models\phi[s]$ is true if and only if $\mathcal A\not\models\alpha[s]$.
* If $\phi$ is $\exists x\alpha$ then $\mathcal A\models\phi[s]$ is true if and only if there is some $a\in A$ such that $\mathcal A\models\alpha[t]$, where $t$ is the modification of $s$ where we let $t(x)=a$.
* If $\phi$ is $\forall x\alpha$ then $\mathcal A\models\phi[s]$ is true if and only if for all $a\in A$ we have $\mathcal A\models\alpha[t]$, where $t$ is the modification of $s$ where we let $t(x)=a$.

Note that if $\sigma$ is a sentence, then no substitution function $s$ is needed (because anything it specifies will eventually be overwritten by the quantifiers). Thus we can write $\mathcal A\models\sigma$ without the $s$.

**Example** Let $\mathcal A$ be the model $(\mathbb Q,<)$ and let $\sigma$ be the sentence $\forall x\forall y\exists z x>y\rightarrow x>z>y$. Then $\mathcal A\models\sigma$ if and only if for all $a\in\mathbb Q$ and for all $b\in\mathbb Q$ we have that there exists $c\in\mathbb Q$ such that $\mathcal A\models x>y\rightarrow x>z>y[x\to a,y\to b,z\to c]$. The latter is true if and only if for all $a,b$ there exists $c$ such that $a>b\implies a>c>b$. This is true since we can always let $c=(a+b)/2$.

We often apply the satisfaction relation to a set of sentences.

**Definition** If $\mathcal L$ is a language of first-order logic, then an $\mathcal L$-theory is a set of $\mathcal L$-sentences.

**Definition** Let $T$ be an $\mathcal L$-theory and let $\mathcal A$ be an $\mathcal L$-structure. We say $\mathcal A\models T$ if for every $\sigma\in T$ we have $\mathcal A\models\sigma$. In this case we also say that $\mathcal A$ is a *model* of $T$.

This fulfills the notion that model theory provides the universes where a given collection of axioms is true. For example if $T$ is group theory, the models of $T$ are groups. If $T$ is set theory, the models of $T$ are universes of set theory.

With the concept of satisfaction in hand, we may further define many semantic notions.

* Semantic validity: A sentence $\sigma$ is *semantically valid* if for every structure $\mathcal A$ we have $\mathcal A\models\sigma$.
* Semantic implication: A sentence $\sigma$ *semantically implies* a sentence $\tau$ if for every model $\mathcal A$ we have $\mathcal A\models \sigma$ implies $\mathcal A\models\tau$.
* Semantic consistency: A theory $T$ is *semantically consistent* if it admits a model $\mathcal A\models T$.

Each of these has syntactic versions involving proofs.

* Syntactic validity: A sentence $\sigma$ is *semantically valid* if there is a proof of $\sigma$.
* Syntactic implication: A sentence $\sigma$ *syntactically implies* a sentence $\tau$ if there is a proof using $\sigma$ of $\tau$.
* Syntactic consistency: A theory $T$ is *semantically consistent* if it cannot be used to derive a falsehood.

We will see that in each case the semantic and syntactic notions are equivalent. Of course this means we have to be very careful to define proof itself properly, something we will do in the next section.

Returning to the semantically valid sentences, we proceed with several examples.

**Example** Every propositional tautology is a semantically valid sentence in the appropriate language. Recall that a propositional tautology is a sentence involving just $0$-ary relations which can be verified by truth tables. For examples, the following are propositional tautologies: $P\wedge Q\to P$; $(P\to Q)\leftrightarrow (\neg P\vee Q)$; $(P\wedge(\mathcal P\to Q))\to Q$.

Similarly, if one begins with a propositional tautology and replaces each propositional variable with a first-order sentence, one obtains a semantically valid sentence.

There are many more examples of semantically valid statements that are genuinely first-order, and don't derive from propositional tautologies.

**Example** The following are semantically valid: $\forall x x=x$; $\forall x R(x)\to\neg\exists x\neg R(x)$; $\forall x\phi(x)\to\phi(\tau)$; $\phi(\tau)\to\exists x\phi(x)$.

#### Formal proofs

An informal proof is an explanation. A formal proof is a sequence of sentences ending with a desired statement. In order to be a correct proof, it must be possible to justify each of the statements in the sequence in one of several ways.

The most obvious way to justify a statement is when it is something we are assuming (an axiom). The next most obvious way is if it is logically apparent, such as a tautology. A somewhat more meaningful step of justification is *modus ponens*, which says that if $\alpha$ is true and $\alpha\to\beta$ is true then $\beta$ is true. 

**Definition** Let $T$ be a theory and $\sigma$ be a sentence of some fixed language $\mathcal L$. We say that $T$ *proves* $\sigma$, written $T\vdash\sigma$, if there exists a sequence of sentences $\sigma_1,\ldots,\sigma_n$ such that $\sigma_n$ is $\sigma$, and for all $i$ we have one of the following:

* $\sigma_i$ is an element of $T$;
* $\sigma_i$ is an instance of a logical axiom (described below);
* there exist $j,k\lt i$ such that $\sigma_k$ is $\sigma_j\to\phi_i$.

We must say what it means for a sentence to be a logical axiom. Given our discussion of valid sentences, it may seem natural to define the logical axioms to be the valid sentences. However this has some disadvantages, since it can be difficult to tell whether a given sentence is valid. Instead we define the logical axioms to be a sufficiently powerful but still easy-to-describe subset of the valid sentences.

**Definition** A sentence $\sigma$ is a *logical axiom* if it is of one of the following types:

* Propositional tautologies
* Universal instantiation: $\forall x\phi(x)\to\phi(\tau)$, for $\tau$ a term without $x$
* Existential generalization: $\phi(\tau)\to\exists x\phi(x)$, for $\tau$ a term without $x$
* Equality: $\forall x\forall y\forall z (x=x)\wedge(x=y\leftrightarrow y=x)\wedge(x=y\wedge y=z\to x=z)$, and $\forall x\forall y x=y\to f(x)=f(y)$, and $\forall x\forall y x=y\to R(x)\leftrightarrow R(y)$, and ditto for all arities.
* Quantifier duality: $\neg\forall x\phi\leftrightarrow \exists x\neg\phi$
* Quantifier distribution: $\forall x(\phi\to\psi)\to(\forall x\phi\to\forall x\psi)$
* Extra quantifier: $\phi\to\forall x\phi$ (where $x$ is not a free variable of $\phi$)

It is easy to see that each of these logical axioms is a valid sentence. There are vastly more valid sentences not in the list. But we will eventually see that the list has enough power to prove the rest of the valid sentences. This was the main criteria used in choosing the axioms!

**Example** We will prove that $T=\emptyset$ proves the sentence $\forall x\exists y x=y$.

1. $\forall x x=x$ (Equality)
2. $\forall x x=x\to \exists y x=y$ (EG)
3. $[\forall x x=x\to \exists y x=y]\to [\forall x x=x\to \forall x\exists y x=y]$ (Quantifier distribution)
4. $\forall x x=x\to \forall x\exists y x=y$ (Modus ponens 2,3)
5. $\forall x\exists y x=y$ (Modus ponens 1,4)

Recall our distinction between semantic truth (satisfaction) and syntactic truth (proofs). The next theorem states that anything we can prove is true. That is, it states that our concept of proof is *sound*.

**Soundness Theorem** If $T\vdash\sigma$ then $T\models\sigma$.

*Proof*. Assume that $\sigma_1,\ldots,\sigma_n$ is a proof from $T$ of $\sigma$. Assume that $\mathcal A\models T$. We will show that for all $i$, we have $\mathcal A\models\sigma_i$. For the base case $i=1$, we know that $\phi_1$ is either in $T$ or a logical axiom. In either case $\mathcal A\models\sigma_1$. Next assume inductively that $\mathcal A\models\sigma_j$ for all $j\lt i$. If $\sigma_i$ is in $T$ or a logical axiom we are done. Otherwise there is $j$ such that $\mathcal A\models\sigma_j$ and $\mathcal A\models \sigma_j\to\sigma_i$. By definition of $\models$ for $\to$, we must have $\mathcal A\models\sigma_i$. This completes the proof because now we know $\mathcal A\models\sigma_n$ which is $\sigma$.

The completeness theorem is the converse of the soundness theorem. Thus it says that everything that is true can be proved. We will prove the completeness theorem in the next section.

The definition of proof that we have given is of theoretical value, but not of great practical value. It can be very difficult to take substantial mathematical results and formalize them in this system. In the rest of the section we mention a few tactics for making the work of finding proofs at least somewhat more accessible.

One common tactic in mathematics is to prove a lemma and use it as a step in a theorem. The next result makes this easy to do.

**Deduction theorem** $T\vdash\alpha\to\beta$ if and only if $T\cup\set{\alpha}\vdash\beta$.

*Proof*. The forward implication is just modus ponens. For the reverse implication, assume that $T\cup\set{\alpha}\vdash\beta$ and let $\sigma_1,\ldots\sigma_n$ be a proof. We will show by induction that for all $i$ we have $T\vdash\alpha\to\sigma_i$.

As before, the base case is trivial. Next assume that $T\vdash\sigma_j$ for all $j\lt i$. If $\sigma_i$ lies in $T$, is $\phi$, or is a logical axiom, then it is clear that $T\vdash\phi\to\sigma_i$. Otherwise $\sigma_i$ followed by modus ponens. By inductive hypothesis, we then have $T\vdash\sigma\to\sigma_j$ and $T\vdash\sigma\to(\sigma_j\to\sigma_i)$. It follows using easy tautologies and modus ponens that $T\vdash\sigma\to\sigma_i$. This completes the induction.

**Proof by contradiction** If $T\cup\set{\neg\sigma}\vdash\alpha\wedge\neg\alpha$, then $T\vdash\sigma$.

*Proof*. If $T\cup\set{\neg\sigma}\vdash\alpha\wedge\neg\alpha$, then using tautologies we have $T\cup\set{\neg\sigma}\vdash\sigma$. By the deduction theorem, $T\vdash \neg\sigma\to\sigma$. By a tautology, $T\vdash\sigma\vee\sigma$ and therefore $T\vdash\sigma$.

**Universal generalization and existential instantiation** Let $c$ be a constant symbol not in $\mathcal L$. If $T\vdash\phi(c)$ then $T\vdash\forall x\phi(x)$. If $T\cup\set{\phi(c)}\vdash\alpha$ then $T\cup\set{\exists x\phi(x)}\vdash\alpha$.

*Proof*. Bleh.

The last two rules formalize common proof notions. The UG rule is for proofs that end "...but c was arbitrary". The EI rule is for proofs that begin "Fix a constant c such that...". In the future we will also use the abbreviations UI and EG as deductive rules corresponding to the logical axioms of the corresponding name.

**Example** We will prove that $T=\emptyset$ proves the sentence $\forall x P(x)\wedge Q(x)\to \forall y P(y)$.

1. We will prove the lemma $\forall x P(x)\wedge Q(x)$ proves $\forall y P(y)$. 
    a. $\forall x P(x)\wedge Q(x)$ (Given)
    c. $P(c)\wedge Q(c)$ (UI)
    d. $P(c)\wedge Q(c)\to P(c)$ (Tautology)
    e. $P(c)$ (MP c,d)
    g. $\forall y P(y)$ (UG)
2. $\forall x P(x)\wedge Q(x)\to \forall y P(y)$ (Deduction, 1)

### 6. Compactness and completeness

Recall that we have proved the Soundness Theorem, which states that any syntactic consequence of $T$ is also a semantic consequence of $T$, that is, if $T\vdash\sigma$ then $T\models\sigma$. In this section we will prove the converse.

**Completeness Theorem, version I** If $T\models\sigma$ then $T\vdash\sigma$.

We will actually prove the completeness theorem in another form. Recall that a theory $T$ is semantically consistent if there is a model of $T$. Recall also that a theory $T$ is syntactically consistent if $T\not\vdash\sigma\wedge\neg\sigma$.

**Completeness Theorem, version II** If $T$ is syntactically consistent, then $T$ has a model.

To see the two statements are equivalent, first suppose that version I is true and let $T$ be a syntactically consistent theory. If $T$ has no models, then $T\models\sigma\wedge\neg\sigma$ is vacuously true, hence $T\vdash\sigma\wedge\neg\sigma$, a contradiction.

Conversely suppose that version II is true and let $T\models\sigma$. Then there is no model of $T\cup\set{\neg\sigma}$, so $T\cup\set{\neg\sigma}$ is syntactically inconsistent. From our proposition on proofs by contradiction, we conclude that $T\vdash\sigma$.

Thus proving the completeness theorem is really about building models. If $T$ is reasonable in the sense that it doesn't lead us to a contradiction, then it should be possible to build a universe in which $T$ is true. This sounds like a somewhat tall order!

The BIG IDEA is to build the model using the terms of the language. In order to illustrate

**Example** Let $\mathcal L=\set{+,\times,0,1,\lt}$ and let $T$ be the standard axioms of arithmetic of the natural numbers (associativity, commutativity, and so on). Our model will include the terms $0$, $1$, $1+1$, $1+1+1$, and so on, pretty good substitutes for the actual natural numbers! Of course there are many other terms such as $1+0+0+1$, but our theory knows that this one is really equivalent to $1+1$. In other words, there is an equivalence relation on terms given by $\tau_1\sim\tau_2$ if and only if $T\vdash\tau_1=\tau_2$.

This example worked smoothly, but we should wonder what we would do if the constant symbol $1$ was not present in the language. We can make a theory in this language that is equivalent to $T$ by defining $1$ as the least natural number greater than $0$. But this language doesn't have any interesting terms. In general when building a model of $T$ we will use the terms of an expanded language where constant symbols have been added for each possible definition.

This idea is called a Henkin construction. In order to begin, we first make a structure from terms.

**Definition** Let $T$ be a theory. The structure $\mathcal H_0=\mathcal H_0(T)$ is defined as follows.

* The domain of $\mathcal H_0$ consists of the terms of $\mathcal L$ with no  variables.
* If $f$ is a function symbol, then $f^{\mathcal H_0}\tau_1\cdots\tau_n$ is defined to be the term $f\tau_1\cdots\tau_n$.
* If $R$ is a relation symbol, then $R^{\mathcal H_0}\tau_1\cdots\tau_n$ is defined to be true if and only if $T\vdash R\tau_1\cdots\tau_n$.

This is a good start, but we have seen this model may have several problems. First, it doesn't identify terms that the theory knows are equivalent. Second, if there aren't any constant symbols in the language, this model will be empty. And third, it still might not be a model of $T$.

**Definition** Let $T$ be a theory. The structure $\mathcal H=\mathcal H(T)$ is defined as follows.

* The domain of $\mathcal H$ consists of the equivalence classes $[\tau]$ of elements of $\mathcal H_0$ with respect to the equivalence relation defined by $\tau_1\sim\tau_2$ if and only if $T\vdash\tau_1=\tau_2$.
* If $f$ is a function symbol, then $f^{\mathcal H}[\tau_1]\cdots[\tau_n]$ is defined to be the equivalence class $[f\tau_1\cdots\tau_n]$.
* If $R$ is a relation symbol, then $R^{\mathcal H}[\tau_1]\cdots[\tau_n]$ is defined to be true if and only if $T\vdash R\tau_1\cdots\tau_n$.

One must check that this definition is well-defined, that is, the function values and relation values are independent of the equivalence class representatives. This can be done using the logical proof axioms pertaining to equality.

**Lemma** If $\sigma$ is an atomic sentence, then $\mathcal H\models\sigma$ if and only if $T\vdash\sigma$.

*Proof sketch*. The key is to show by induction that $\mathrm{val}_{\mathcal H}(\tau)=[\tau]$ for all terms $\tau$. Then If $\sigma$ is the sentence $R\tau_1\cdots\tau_n$, our definition of $R^{\mathcal H}$ guarantees the desired result. $\blacksquare$

We are clearly on our way to obtaining a model of $T$. But quantifiers are still a big problem.

**Example** Let $\mathcal L=\set{\lt,a,b}$, where $a,b$ are constant symbols, and let $T$ be the theory of $\omega$. Then $\mathcal H$ has domain $\set{a,b}$ but the model does not decide whether $a\lt b$ or $b\lt a$. Thus the theory $T$ includes trichotomy but the model $\mathcal H$ does not satisfy trichotomy.

To fix this problem, we will work only with complete theories $T$.

**Definition** A theory $T$ is *complete* if for every sentence $\sigma$ we have either $\sigma\in T$ or $\neg\sigma\in T$.

**Lemma** If $T$ is a syntactically consistent theory, there exists a complete syntactically consistent theory $\bar T$ such that $T\subset\bar T$.

*Proof*. Let $P$ be the partial order consisting of all syntactically consistent theories $U$ extending $T$. Then $P$ is partially ordered by set inclusion. Then chains of $P$ are bounded because the union of a chain of syntactically consistent theories is still syntactically consistent.

By Zorn's lemma, there exists a maximal consistent theory $\bar T$. such that $T\subset\bar T$. We claim that $\bar T$ is complete. Indeed, if $\sigma\notin\bar T$, then $\bar T\cup\set{\sigma}$ is inconsistent, so by our theorem about proofs by contradiction, $\bar T\vdash\neg\sigma$. Since $\bar T$ is maximal, it follows that $\neg\sigma\in T$. $\blacksquare$

We remark that if $T$ is a complete theory $\alpha\vee\beta\in T$, then we must have either $\alpha\in T$ or $\beta\in T$. Thus if we revisit the above example and complete $T$ before building $\mathcal H$, we will either have $a\lt b$ or $b\leq a$, whichever Zorn's lemma picks for us.

But there is still one big issue left to address. Continuing the above example, let $T$ be the theory of $\omega$ together with the sentences $a$ has three predecessors and $b$ has four. Then our model $\mathcal H$ will satisfy $a\lt b$, but it still will not satisfy the sentence $\exists x x\lt a$.

Generally speaking, a given language may not have enough terms to make $\mathcal H$ a real model of $T$. In order to fix this, we need to add new terms, constant symbols, that witness existential formulas.

**Definition** A theory $T$ is said to have *witnessing terms* if whenever $\phi(x)$ is a formula with one free variable $x$ there exists a term $\tau$ such that $T\vdash\exists x\phi(x)\to\phi(\tau)$.

For example consider $\mathbb R$ as a field. If $\phi(x)$ is $\forall y xy=y+y$ then a witnessing term would be $1+1$. If $\phi(x)$ is $xx=1+1$ then there is no witnessing term and we will need to add one. The following is the crux of the Henkin construction.

**Lemma** If $T$ is a syntactically consistent theory, then there exists a syntactially consistent theory $T'$ in an expanded language such that $T\subset T'$ and $T'$ has witnessing terms.

Assuming this lemma is true, let us outline the proof of the Completeness Theorem.

Given a syntactically constistent theory, we first extend it to a theory with witnessing terms, and then to a complete theory $T^\ast$ in the expanded language. We let $\mathcal H$ be the Henkin model corresponding to $T^\ast$.

We must prove that $\mathcal H$ is a model of $T^\ast$ and hence of $T$. This is done by induction on the complexity of the sentence (not the length). We have already addressed atomic sentences. The difficult part is the $\exists$ quantifier step, but noe can use the witnessing property in this part!

#### Completeness and its consequences

We still owe the proof of the lemma.

**Lemma** If $T$ is a syntactically consistent theory, then there exists a syntactially consistent theory $T'$ in an expanded language such that $T\subset T'$ and $T'$ has witnessing terms.

*Proof*. We first show how to add a witnessing term for a single formula $\exists x\phi(x)$. To do this, we let $\mathcal L'=\mathcal L\cup\set{c}$, and let $T'=T\cup\set{\exists x\phi(x)\to\phi(c)}$.

We claim that $T'$ is syntactically consitent. If it isn't, then there is a proof from $T'$ of a contradictory sentence $\alpha\wedge\neg\alpha$. By the proof-by-contradiction theorem, there is a proof from $T$ of $\neg(\exists x\phi(x)\to\phi(c))$. Using a tautology, there is a proof from $T$ of $\exists x\phi(x)$ and a proof from $T$ of $\neg\phi(c)$. By UG, there is a proof from $T$ of $\forall x\neg\phi(x)$. This is clearly a contradiction, establishing the claim.

Now to add witnessing terms for all formulas, we inductively define $\mathcal L^{(n)},T^{(n)}$ as follows. Firstlet $\mathcal L^{(0)}=\mathcal L$ and $T^{(0)}=T$. If $\mathcal L^{(n)},T^{(n)}$ have been defined, we let $\mathcal L^{(n+1)}$ include new constant symbols for each existential formula of $\mathcal L^{(n)}$, and let $T^{(n+1)}$ include corresponding sentences for each. Then by an argument similar to the above, each $\mathcal T^{(n)}$ is syntactically consistent, and it follows that $T'=\bigcup\mathcal T^{(n)}$ is syntactically consistent. Moreover with $T'$ we have "caught our tail" meaning that $T'$ has witnessing terms. $\blacksquare$

**Completeness Theorem, version II** If $T$ is syntactically consistent, then $T$ has a model.

*Proof*. We apply the lemmas we have proved in sequence. Given $T$, we first extend it to a theory with witnessing terms and then further extend it to a complete theory $T^\ast$ in the expanded language. We then let $\mathcal H$ be the Henkin/Herbrand model of $T^\ast$. 

We claim that for all sentences $\sigma$ we have $\sigma\in T^\ast$ if and only if $\mathcal H\models\sigma$, so that $\mathcal H$ really is a model of $T^\ast$. For this we proceed by induction on the *complexity* of $\sigma$. For this we can assume that the only connectives in $\sigma$ are $\wedge,\neg,\exists$ and proceed by indnuction on the number of occurrences of these symbols.

We have already proved the result for atomic sentences $\sigma$ directly from the definition of $\mathcal H$.

If $\sigma$ is of the form $\neg\alpha$, then the result follows from the inductive hypothesis for $\alpha$ and the completeness of $T^\ast$. Indeed, we have $\sigma\in T^\ast$ iff $\alpha\notin T^\ast$ iff $\mathcal H\not\models\alpha$ iff $\mathcal H\models\sigma$. Similarly if $\sigma$ is of the form $\alpha\wedge\beta$ then the result is immediate from the inductive hypothesis for $\alpha$ and $\beta$ and the completness of $T^\ast$.

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

We remark that the :) follows from the definition of the Henkin/Herbrand model. Since we don't have control over the length of the term $\tau$, we had to do our induction over the complexity of $\sigma$ instead of the length of $\sigma$.

The completeness theorem has many consequences, one of which is to greatly simplify our terminology.

* Semantic validity is equivalent to syntactic validity.
* Semantic implication is equivalent to syntactic implication.
* Semantic consistency is equivalent to syntactic consistency.

As a result we rarely need to discern between the semantic and syntactic notions. Another simple but powerful consequence is the following.

**Compactness Theorem** If every finite subset of $T$ has a model, then $T$ has a model.

*Proof*. It suffices to show that if every finite subset of $T$ is syntactically consistent, then $T$ is syntactically consistent. Taking the contrapositive, we must show that if $T$ is syntactically inconsistent then some finite subset of $T$ is syntactically inconsistent. This is clear from the fact that proofs are finite: if $T$ proves a contradictory sentence $\alpha\wedge\neg\alpha$, then the proof used just finitely many sentences of $T$, so there exists a finite subset $T_0\subset T$ that proves a $\alpha\wedge\neg\alpha$ too. $\blacksquare$

The compactness theorem is a powerful tool for generalizing proofs about finite objects into proofs about infinite objects.

**Corollary** Suppose $T$ has arbitrarily large finite models. Then $T$ has infinite models.

*Proof*. Let $\sigma_n$ be the sentence which says that there exist $n$ distinct elements of the universe. That is, $\sigma_n$ says that $\exists x_1\cdots\exists x_n\bigwedge x_i\neq x_j$. Let $T'$ be the theory $T\cup\set{\sigma_n:n\in\mathbb N}$. Then every finite subset of $T'$ is consistent by our hypothesis. As a consequence $T'$ is consistent. Any model of $T'$ is a model of $T$ and is infinite. $\blacksquare$

This simple idea can also be used to derive the following consequences of compactness. The first is key in the theory of *nonstandard arithmetic*, where one studies models of number theory with infinite elements, and the second fact is key in *nonstandard analysis* where one studies models of analysis with infinitesimal elements.

**Corollary** Let $T$ be the theory of the natural numbers, that is, the set of sentences true in the structure $(\mathbb N;+,\times,0,1,\lt)$. There is a model of $T$ with an element $N$ such that $n\lt N$ for all $n\in\mathbb N$.

**Corollary** Let $T$ be the theory of the real numbers, that is, the set of sentences true in the structure $(\mathbb R;+,\times,0,1,\lt)$. There is a model of $T$ with an element $\epsilon$ such that for all $0\lt r\in\mathbb R$ we have $0\lt\epsilon\lt r$.

We will leave the proofs as exercises.

### 7. Applications of compactness, more about theories

For the next result, recall that the theory of simple graphs is the theory of a single binary relation $\sim$ which is irreflexive and transitive. Further recall that a graph $G$ is *bipartite* if it can be partitioned into subsets $P,Q$ such that no two vertices of $P$ are adjacent and no two vertices of $Q$ are adjacent. For example, a hexagon is bipartite but a heptagon is not.

**Corollary** Let $G$ be a graph such that every finite subset of $G$ is bipartite. Then $G$ is bipartite.

*Proof*. Let the language $\mathcal L$ consist of $\sim$ together with constant symbols $c_x$ for every $x\in G$ together with unary relation symbols $P$ and $Q$. Let the theory $T$ consist of the following axioms:

* $c_x\neq c_{x'}$ whenever $x\neq x'$
* $c_x\sim c_{x'}$ whenever $x\sim x'$
* $c_x\not\sim c_{x'}$ whenever $x\not\sim x'$
* $P,Q$ is a partition
* $P,Q$ have no edges within them

Then every finite subset of $T$ is consistent. Indeed, if $T_0$ is a finite subset of $T$, then $T_0$ mentions a certain subset $G_0\subset G$. The induced subgraph corresponding to $G_0$ is bipartite and thus gives rise to a model of $T_0$.

By the compactness theorem, $T$ has a model, $G'$. Observe that $G$ is a subgraph of $G'$ via the function which sends any $x\in G$ to the interpretation of $c_x$ in $G'$. Since $G'$ is bipartite, it follows that $G$ is bipartite. $\blacksquare$.

For each theory $T$ there is a corresponding class of models of $T$. We will say that a class $\mathcal C$ of structures is *axiomatizable* if there exists a theory $T$ such that the models of $T$ are precisely the elements of $\mathcal C$. It is natural to ask whether every (reasonable) class of srtuctures is axiomatizable. Our next result says that the answer is no.

Recall that a graph is *connected* if for any two vertices $x,y$, there exists a path from $x$ to $y$. That is, for any $x,y$ there is a sequence of vertics $x_1,\ldots,x_n$ such that $x\sim x_1\sim x_2\sim\cdots\sim x_n=y$.

**Corollary** The class of connected graphs is not axiomatizable.

*Proof*. Suppose there exists a theory $T$ such that the models of $T$ are exactly the connected graphs. Expand the language with two new constant symbols $a,b$. Let $\sigma_n$ be the sentence which says there is no path from $a$ to $b$ of length $n$. Let $T'$ be the theory $T\cup\set{\sigma_n:n\in\omega}$. Then any finite subset $T_0\subset T'$ is consistent. Indeed, if $N$ is the largest number such that $\sigma_N$ occurs in $T_0$, then a graph consisting of a single path of length $N+1$ from $a$ to $b$ gives a model of $T_0$. It follows from the compactness theorem that $T'$ is consistent and hence has a model. But any model of $T'$ is disconnected, because there cannot be a path from $a$ to $b$. Hence we have shown that there is a disconnected model of $T$, a contradiction. $\blacksquare$

**Corollary** The class of well-orders is not axiomatizable.

*Proof*. Suppose there exists a theory $T$ such that the models of $T$ are exactly the well-orders. Expand the language with new constant symbols $c_n$ for $n\in\omega$. Let $\sigma_n$ be the sentence which says that $c_n\lt\ldots\lt c_0$. Let $T'$ be the theory $T\cup\set{\sigma_n:n\in\omega}$. Then any finite subset $T_0\subset T'$ is consistent. Indeed, if $N$ is the largest number such that $\sigma_N$ occurs in $T_0$, then the structure $(\omega,\lt)$ together with a decreasing sequence of interpretations of $c_0,\ldots,c_n$ is a model of $T_0$. It follows from the compactness theorem that $T'$ is consistent and hence has a model. But any model of $T'$ is ill-founded, because the interpretations of the $c_n$ form an infinite decreasing sequence. Hence we have shown that there is an ill-founded model of $T$, a contradiction. $\blacksquare$

Recall we have shown that theories with arbitrarily large finite models have infinite models. It is natural to ask what cardinalities will occur. Our final corollary addresses this question with the most generous possible answer.

**Lowenheim–Skolem Theorem** Suppose $T$ is a theory in a language $\mathcal L$ and $T$ has an infinite model. Then for any cardinal $\kappa\geq\abs{\mathcal L}\cdot\aleph_0$, $T$ has a model of cardinality $\kappa$.

*Proof*. We prove the theorem in two parts: a downwards direction and an upwards direction. To begin with downwards direction, we will prove that if $T$ has an infinite model then $T$ has a model of size $\abs{\mathcal L}\cdot\aleph_0$. Reading the proof of the completeness theorem, we see that the Henkin/Herbrand model $\mathcal H$ happens to have precisely this size. Indeed, it is constructed from terms, which are finite strings of elements of the given countable language.

For the upwards direction, assume $T$ has a model of size $\abs{\mathcal L}\cdot\aleph_0$ and let $\kappa\geq\abs{\mathcal L}\cdot\aleph_0$ be given. Expand the language to include $\kappa$ many constant symbols $c_\alpha$ for $\alpha\lt\kappa$. Let $T'=T\cup\set{c_\alpha\neq c_\beta\mid\alpha\neq\beta}$. Then any finite subset $T_0\subset T'$ is consistent. Indeed, $T_0$ mentions just finitely many of the constant symbols $c_\alpha$, and we can intrepret them as arbitrary elements of the given model of $T$. It follows from the compactness theorem that $T'$ is consistent, and so has a model. The resulting model must have cardinality at least $\kappa$. If it has cardinality greater than $\kappa$, we can use the downwards direction of the theorem to produce a model of cardinality exactly $\kappa$. $\blacksquare$

The Lowenheim–Skolem theorem has the mind-bending consequence that if ZFC is consistent, then ZFC has a countable model. Since we know that ZFC implies there exist uncountable sets, we appear to have reached a paradox: an uncountable object is contained in a countable object. The resolution to this apparent contradiction is that the countable model only believes its sets are uncountable because it lacks the bijections to prove they are countable. These bijections do exist but externally to the model.

#### Complete theories

Previously we said that a theory $T$ is complete if it is consistent, and for every sentence $\sigma$ either $\sigma\in T$ or $\neg\sigma\in T$.

For example, if $\mathcal A$ is any structure then the theory $T=Th(\mathcal A)$ consistening of all sentences $\sigma$ such that $\mathcal A\models\sigma$ is a complete theory. This follows simply from the definition of $\models$. Thus the theory of arithmetic $Th(\mathbb N,+,\times)$ and the theory of analysis $Th(\mathbb R,+,\times)$ are complete theories.

In accordance with common practice, we also say that $T$ is complete if the set of logical consequences of $T$ is complete. That is, $T$ is *complete* if it is consistent and for every sentence $\sigma$ either $T\models\sigma$ or $T\not\models\sigma$.

For example, if $T$ is the theory which says that $G$ is a group with exactly $7$ elements, then $T$ is complete. (One shows in a standard algebra class that there is only one such group.)

On the other hand, most theories are not complete. For example the theory of infinite linear orders (is there a last element? consider $(0,1)$ versus $(0,1]$), the theory of infinite abelian groups (are all elements divisible by 2? consider $\mathbb Z$ versus $\mathbb Q$), and set theory (does CH hold?).

In these examples, we can find sentences $\sigma$ such that $T\cup\set{\sigma}$ has a model, so $\neg\sigma$ is not a consequence of $T$, and $T\cup\set{\neg\sigma}$ has a model, so $\sigma$ is not a consequence of $T$.

But how can one show that a given theory $T$ is complete? In general this can be a challenging problem, but in the rest of this section, we will give one relatively easy tool to prove that at theory is complete. We first need several new definitions.

**Definition** Structures $\mathcal A,\mathcal B$ are *isomorphic* if there is a bijection $\phi\colon A\to B$ such that for every function symbol $f$ we have $f^{\mathcal A}(a)=b\iff f^{\mathcal B}(\phi(a))=\phi(b)$ and for every relation symbol $R$ we have $R^{\mathcal A}(a)\iff R^{\mathcal B}(\phi(a))$.

**Definition** Structures $\mathcal A,\mathcal B$ are *elementarily equivalent* if they satisfy the same sentences: $\mathcal A\models\sigma\iff\mathcal B\models\sigma$. In other words, the two structures are models of the same complete theory.

It is clear that if structures $\mathcal A,\mathcal B$ are isomorphic then they are elementarily equivalent. However the converse is false, since for example if $T$ is any complete theory with infinite models then $T$ has models of distinct cardinalities. This means that structures can have properties that are not described by first-order logic!

In light of the example in the previous paragraph, it is natural to ask whether a complete theory can have distinct models of the same cardinality. In general this is not the case, but when it is true we give it a name. 

**Definition** Let $T$ be a theory and let $\kappa$ be a cardinal. Then $T$ is called *$\kappa$-categorical* if all models of $T$ of cardinality $\kappa$ are isomorphic to one another.

The following is the most famous example of a categorical theory. The theory of dense linear orders without endpoints consists of the theory of linear orders (irreflexivity, transitivity, trichotomy) plus the axioms $\forall x\forall y\exists z x\lt y\rightarrow x\lt z\lt y$ and $\forall x\exists y\exists z y\lt x\lt z$. Thus the rational order is an example of a dense linear order without endpoints.

**Proposition** The theory $T$ of dense linear orders without endpoints is $\aleph_0$-categorical.

*Proof sketch*. Let $\mathcal A,\mathcal B$ be two countable models $T$. Let $a_n$ enumerate $A$ and let $b_n$ enumerate $B$. We can recursively construct an isomorphism using the "back-and-forth" method. Initially let $\phi(a_0)=b_0$. Next assume $\phi$ has been defined on $a_0,\ldots,a_n$ and $\phi^{-1}$ has been defined on $b_0,\ldots,b_n$. We then define $\phi$ on $a_{n+1}$ and $\phi^{-1}$ on $b_{n+1}$ by mapping them to the interval required to preserve the order relations. $\blacksquare$

Note that the theory of dense linear orders without endpoints is not $\kappa$-categorical for $\kappa=2^{\aleph_0}$. For example $\mathbb R$ and $\mathbb R\setminus\set{0}$ are dense linear orders without endpoints that are not isomorphic to one another.

Next we describe an example of a theory that is $\kappa$-categorical for some uncountable $\kappa$. A group is called torsion-free if it satisfies $\forall x x\neq0\rightarrow nx\neq 0$. A group is called divisible if it satisfies $\forall x\exists y nx=y$. The torsion-free divisible abelian groups are simply direct sums of copies of $\mathbb Q$. 

**Proposition.** The theory $T$ of torsion-free divisible abelian groups is $\aleph_1$-categorical.

*Proof*. Any torsion-free divisible abelian group $G$ can be made into a rational vector space by defining $\frac mng=h$ iff $mg=nh$. Note that divisibility is used to show there is such an $h$, and torsion-free is used to show that $h$ is unique. Now any two uncountable vector spaces over a countable field must have the same dimension, and therefore are isomorphic to one another. $\blacksquare$

The following result shows the connection between categorical and complete theories.

**Vaught Test Thoerem** Let $T$ be a consistent theory in a finite language with no finite models. If $T$ is $\kappa$-categorical for some $\kappa$, then $T$ is complete.

*Proof*. Suppose that $T$ is $\kappa$-categorical but not complete. Then there is a sentence $\sigma$ such that both $T\cup\set{\sigma}$ and $T\cup\set{\neg\sigma}$ are consistent. By the Lowenheim–Skolem theorem, there are models $\mathcal A,\mathcal B$ of $T\cup\set{\sigma},T\cup\set{\neg\sigma}$ respectively, of cardinality $\kappa$. This contradicts that $T$ is $\kappa$-categorical. $\blacksquare$

**Corollary** The theory of dense linear orders without endpoints is complete. In particular, $(\mathbb Q,\lt)$ and $(\mathbb R,\lt)$ are elementarily equivalent.

**Corollary** The theory of torsion-free divisible abelian groups is complete. In particular, $(\mathbb Q,+)$ and $(\mathbb R,+)$ are elementarily equivalent.

A famous theorem of Morley states that a theory $T$ is $\kappa$-categorical for some $\kappa\geq\aleph_1$ if and only if $T$ is $\aleph_1$-categorical. This means that there are just two types of categoricity, countable and uncountable.

## Part III: Computability theory and incompleteness

### 8. Definability, absoluteness, and computability

Consider the structure $(\mathbb N,+,0)$, and compare it with the structure $(\mathbb N,+)$. The second structure has a reduced language, but is it really weaker in the sense that fewer concepts are expressible?

**Definition** Let $\mathcal A$ be a structure. An $n$-ary relation $R\subset A^n$ is *definable* in $\mathcal A$ if there is a formula $\phi(x_1,\ldots,x_n)$ such that $(a_1,\ldots,a_n)\in R\iff\mathcal A\models\phi[x_i=a_i]$. A function $f\colon A^n\to A$ is definable if its graph is a definable $n+1$-ary relation. Finally an element $c\in A$ is definable if $\set{c}$ is a definable unary relation.

For example, if $\mathcal A=(\mathbb N,+)$. Then the constant $0$ is definable using $x+x=x$, and $\lt$ is definable using $\exists z x+z=y$.

**Definition** Let $T$ be an $\mathcal L$-theory, and $\phi$ a formula. Then the corresponding *expansion by definitions* of $T$ is the theory $T\cup\set{\phi(x_1,\ldots,x_n)\iff R(x_1,\ldots,x_n}$, where $R$ is a new $n$-ary relation symbol.

If $T'$ is an expansion by definitions of $T$, then $T,T$ prove exactly the same sentences of the original language. Moreover if $\phi$ is any formula of the expanded language then $T$ proves it is equivalent to a formula of the original language. Finally, if $\mathcal A$ is any model of $T$ then $\mathcal A$ can be expanded to a model of $T'$.

In the rest of this section we study definability in models of set theory. That is, we will return to our favorite theory ZFC and its fragments. Something potentially confusing happens when we study models of set theory that didn't happen in other theories: we can try use a set with its native $\epsilon$ relation as a model of set theory.

**Definition** Let $A$ be any set. Then $A$ gives rise to a *set model* $(A;\epsilon)$ with domain $A$ and binary relation $\epsilon$.

When we work with set models, we elide the structure notation $\mathcal A=(A;\epsilon)$ and simply write $A$. Of course most set models will not satisfy all ZFC, but some subtheory of ZFC. For instance, every set model satisfies the Axiom of Extensionality.

One of the most useful set models is the set HF of hereditarily finite sets, also denoted $V_\omega$. Observe that HF satisfies all of ZFC except the Axiom of Infinity. Similarly the model $HC$ consisting of the hereditarily countable sets satisfies all of ZFC 

When $A,B$ are set models and $A\subset B$, both models believe they are talking about some of the same objects (they share the elements of $A$ in common), but they may disagree about properties of these objects. For example $\omega\subset HF$, the two models agree on which object is the empty set, and disagree on whether $\epsilon$ is a linear order. An even worse example is $\set{3,4,5,\ldots}$, which disagrees with HF about which object is the empty set!

**Definition** Let $A\subset B$ be sets. A formula $\phi(x_1,\ldots,x_n)$ is *absolute* between $A$ and $B$ if for all substitution functions $s\colon V\to A$ we have $\mathcal A\models\phi[s]\iff\mathcal B\models\phi[s]$.

Which formulas are absolute between which set models? This is a complicated question in general, but there is a large class of formulas that is absolute between any two set models which are transitive. Recall that a set $A$ is *transitive* if $b\in a\in A$ implies $b\in A$.

**Definition** A formula $\phi$ is said to be a *$\Delta_0$-formula* if its quantifiers are bound, that is, every occurrence of $\exists$ is of the form $\exists y\in z$ and every occurrence of $\forall$ is of the form $\forall y\in z$.

For example, the proposition that $x$ is an ordered pair may be expressed as a $\Delta_0$-formula. One needs to say $\exists y,z\in\bigcup x x=\langle y,z\rangle$.

On the other hand, the proposition that $x$ is a power set of another set cannot (apparently) be expressed as a $\Delta_0$ formula.

**Theorem** If $A,B$ are transitive sets and $A\subset B$, then for any $\Delta_0$-formula $\phi$ we have that $\phi$ is absolute between $A$ and $B$.

*Proof*. We use induction on the complexity of $\phi$. If $\phi$ is atomic then it is of the form $x=y$ or $x\in y$. In each case the statement holds because both sets are using the true equality and element relations.

If $\phi$ is $\neg\alpha$ then the inductive hypothesis for $\alpha$ clearly gives the corresponding statement for $\phi$. A similar argument holds for the binary connectives.

If $\phi$ is $\exists y\in z\alpha$ and the statement is true of $\alpha$ then we have:

$$\begin{aligned}
A\models \exists y\in z\alpha(x,y,z)
  &\iff \exists a\in A A\models \alpha(x,a,z)\wedge a\in z\\
  &\iff \exists a\in B B\models \alpha(x,a,z)\wedge a\in z\\
  &\iff B\models \exists y\in z\alpha(x,y,z)
\end{aligned}$$

Here in the backwards direction we are using transitivity to say that if $a\in B$ and $a$ is required to be in $z\in A$, then $a\in A$. $\blacksquare$

#### Computability

Suppose we are working over the set model HF. Informally, we say that $A$ is *decidable* if there is a procedure that decides given $x$ whether or not $x\in A$. In other words, there should be an algorithm or computer program which takes input $x$ and halts and outputs Yes if $x\in A$ and halts and outputs No if $x\notin A$.

For example, if $\phi$ is a $\Delta_0$-formula. Let $A=\set{x\in HF\mid \phi(x)}$ be the  corresponding $\Delta_0$-definable subset. Then $A$ is very simple in the sense that there is a natural decision procedure to decide whether or not $x\in A$. One simply steps through the formula testing its conditions, and each time one encounters a bounded quantifier, one must undertake just a finite search.

On the other hand, there are sets that are intuitively computable but not $\Delta_0$-definable. For example, let $A$ be the set of even natural numbers. Then there is cleary a decision procedure for $A$: given $x$ first check whether it is totally ordered and transitive, then mark off elements in pairs until you have $0$ or $1$ left over. But $A$ is not $\Delta_0$-definable. To see this, note that if it were then since $\omega$ is transitive it would be definable in $\omega$. But using compactness, $\omega$ has an elementary extension with an automorphism that moves $A$. Thus $A$ is not definable in $\omega$, and hence it is not $\Delta_0$-definable in HF.

**Definition** A formula $\phi$ is $\Sigma_1$ if it is of the form $\exists y\alpha$, where $\alpha$ is $\Delta_0$. A formula $\phi$ is $\Pi_1$ if it is of the form $\forall y\alpha$, where $\alpha$ is $\Delta_0$. (We may also allow iterated existentials or iterated universals.)

**Definition** A subset $A$ of HF is $\Delta_1$ definable if it is both $\Sigma_1$-definable and $\Pi_1$-definable.

(In fact there is a whole hierarchy of Sigma, Pi, and Delta definability, but this is all we will need for now.)

For example, the set $A$ of even natural numbers is a $\Delta_1$-definable subset of HF. We have already said that the property of being a natural number is $\Delta_0$-definable in HF. Thus the formula $\alpha(n,e)$ which says "$n$ is a natural number and $e$ is the set of even numbers $\lt n$" is $\Delta_0$. Then $x\in A$ if and only if $\exists n,e\alpha(n,e)\wedge x\in e$, and $x\in A$ if and only if $\forall n,e\alpha(n,e)\wedge x\in n\rightarrow x\in e$.

Like the $\Delta_0$-formulas, the $\Delta_1$-decidable sets enjoy a degree of absoluteness.

**Proposition** Let $A,B$ be transitive sets and $A\subset B$. If $\phi$ is a $\Sigma_1$ sentence and $A\models\phi$ then $B\models\phi$. If $\phi$ is a $\Pi_1$ sentence and $B\models\phi$ then $A\models\phi$. If $\phi$ is $\Sigma_1$, $\psi$ is $\Pi_1$, and both $A,B$ model $\phi\leftrightarrow\psi$, then $\phi,\psi$ are absolute between $A$ and $B$.

Like the $\Delta_0$-definable sets, the $\Delta_1$-definable sets are decidable, but by a more complex procedure. Suppose that $A$ is defined both by $\exists y\alpha(x,y)$ and by $\forall y\beta(x,y)$, where $\alpha,\beta$ are $\Delta_0$-formulas. Then $A^c$ is defined by $\exists y\neg\beta(x,y)$. Given an input $x$, we run through all possible values of $y$ and each time check whether $\alpha(x,y)$ holds and whether $\neg\beta(x,y)$ holds. Since $A$ and $A^c$ are complementary, one of these must eventually occur, at which point we can say whether $x\in A$ or $x\in A^c$. Note that this procedure will have to terminate, but our description provides no insight as to when.

Conversely, if a set $A$ is decidable by some procedure, then $A$ should be $\Delta_1$-definable. To see this note that each run of the procedure should leave some record of its behavior. Thus we can say that $x\in A$ iff there exists a code for a run of the procedure on input $x$ that halted and output Yes. And we can say that $x\in A$ iff for all codes for a run of the procedure on input $x$, if the code halted, then the output was Yes.

**Church-Turing Thesis** A set is decidable by a procedure (in a finite amount of time, with finitary operations, without resource limitations) if and only if it is $\Delta_1$-definable.

In other words, all "reasonable" notions of being decidable by a procedure end up being equivalent to one another. The list of equivalent notions is long and includes decidable by a Turing machine, decidable by a python program, definable by recursion, and so forth. The point is that all of these possible choices lead to the same robust notion. For our class we will stick with $\Delta_1$-definable as the official definition.

**Definition** A subset $A$ of HF is *decidable* if it is $\Delta_1$-definable.

The class of decidable sets has many nice properties.

**Proposition** The decidable sets of HF are closed under boolean operations and bounded quantification.

*Proof*. It suffices to show that $\Delta_1$-definitions are closed under negation, conjunction, disjunction, and bounded quantification.

Complementation is clear because $\Sigma_1$ and $\Pi_1$ are dual to one another. For disjuctions observe that $\exists x\alpha(x)\wedge\exists x\beta(x)$ is equivalent to $\exists x\exists y\alpha(x)\wedge\beta(y)$, and similarly for $\forall$. Yet another similar argument holds for conjuctions.

For bounded quantification, we will show that $\Sigma_1$ is closed under bounded quantification. The argument for $\Pi_1$ is similar, and the fact for $\Delta_1$ follows. For this, first observe that $\exists x\in y\exists z\alpha$ is equivalent to $\exists z\exists x\in y\alpha$ which is clearly $\Sigma_1$. Next we claim that $\forall x\in y\exists z\alpha$ is equivalent to $\exists u\forall x\in y\exists z\in u\alpha$. The backward implication is trivial. For the forward implication we create a set $u$ which contains a witness $z_x$ for all possible $x\in y$. $\blacksquare$

### 9. Computable functions, recursion, undecidable sets

**Definition** Let $f$ be a function from HF to HF. Then $f$ is *computable* if its graph is decidable.

The Church--Turing thesis implies that we can informally say that $f$ is computable if and only if there is a procedure which, given any input $x$, halts and outputs $f(x)$. To see this equivalence, first if the graph of $f$ is decidable then given $x$ we can search through all possible values $y$ until we find one with $(x,y)\in f$ and then we can halt and output $y$. Conversely if there is such a procedure for evaluating $f$ then given $(x,y)$ we can decide whether $(x,y)\in f$ by calculating $f(x)$ and asking whether $f(x)=y$.

The simplest example of a computable function is the characteristic function $\chi_A$ of any decidable set $A$. Indeed $(x,i)\in\chi_A$ if and only if $i=1$ and $x\in A$ or else $i=0$ and $x\notin A$. This statement is a boolean combination of $\Delta_1$-formulas.

Another example of a computable function is the cardinality function $f(x)=\abs{x}$. Here $\abs{x}=y$ if and only if $y\in\omega$ and there exists a bijection between $x$ and $y$, and $\abs{x}=y$ if and only if $y\in\omega$ and every injection from $x$ to $y$ is a surjection.

Some more interesting examples of computable functions are $+,\cdot$. However to prove this we will need the recursion theorem. You may recall that we have proved the classical recursion theorm and the transfinite recursion theorem. What we need is the computable version of the recursion theorem.

**Theorem** If $G\colon\mathbb N^{\lt\omega}\to\mathbb N$ is computable, then there exists a computable function $F\colon\mathbb N\to\mathbb N$ such that $F(n)=G(F\restriction n)$.

*Proof idea*. The ordinary recursion theorem implies that the function $F$ exists. To see that $F$ is computable observe that $F(n)=y$ if and only if there exists a finite partial function $f$ obeying the recursion and satisfying $f(n)=y$, and $F(n)=y$ if and only if for all finite partial functions $f$ obeying the recursion if $n$ is in the domain then $f(n)=y$. Thus the graph of $F$ is $\Delta_1$-definable. $\blacksquare$

Thus the well-known enumerations such as $n!$, the $n$th Fibonacci number, as well as $+,\cdot$ are computable because they are defined recursively by computable rules. There is also a version of the recursion theorem along $\in$, so that functions such as the cardinality and rank functions may be defined recursively.

Another application of the recursion theorem is the following.

**Proposition** Let $A$ be the set consisting of all pairs $\phi,\sigma$, where $\phi$ is a code for a $\Delta_0$-formula and $\sigma$ is a substitution function, such that $HF\models\phi[\sigma]$. Then $A$ is decidable.

The idea of the proof is to use the partial order of subformulas, and then to define a function $f$ which maps inputs $\phi,\sigma$ to values $T,F$ by recursion. The recursive definition $G$ is simply a formalizing our definition of satisfaction.

#### Undecidable sets

We have given numerous examples of decidable sets and computable functions. What kinds of things are not decidable? We first begin with the following.

**Theorem** There exists a set which is $\Sigma_1$-definable but not $\Delta_1$-definable.

This theorem is hardly surprising, since otherwise we would probably not have given different names to the concepts $\Delta_1$ and $\Sigma_1$. To prove this we will first show that there is a $\Sigma_1$ set which is universal in the sense that it is of maximum complexity among the $\Sigma_1$ sets. We will then prove that a universal $\Sigma_1$ set cannot be $\Delta_1$.

**Lemma** There exists a $\Sigma_1$-definable set $U\subset HF^2$ such that for every $\Sigma_1$-definable set $A\subset HF$ there exists $r\in HF$ such that $A=\set{x\mid (r,x)\in U}$.

*Proof of Lemma*. Let $V$ be the set of all triples $(\phi,x,y)$ where $\phi$ is a code for a $\Delta_0$-formula and $HF\models\phi(x,y)$. Then we have shown $V$ is $\Delta_1$. Next let $U$ be the set of all pairs $(\phi,x)$ such that $\exists y(\phi,x,y)\in V$. Then $U$ is clearly $\Sigma_1$.

Now if $A$ is any $\Sigma_1$ set, then $A$ is defined by $x\in A$ if and only if $\exists y\phi(x,y)$ for some $\phi$. Thus $A$ is precisely $\set{x\mid(\phi,x)\in U}$, as desired. $\blacksquare$

To prove the theorem, we once again return to the diagonalization idea of Cantor and Russell.

*Proof of Theorem*. Let $U$ be a universal $\Sigma_1$ set. Let $D=\set{x\in HF\mid (x,x)\notin U}$. Then $D$ fails the conclusion of the Lemma, since it disagrees with every horizontal section of $U$. Thus $D$ is not $\Sigma_1$. However the definition of $D$ is clearly $\Pi_1$. It follows that $HF\setminus D$ is a $\Sigma_1$ set which is not $\Pi_1$ and in particular not $\Delta_1$, as desired. $\blacksquare$

While the universal set the first place one would look for an example of an undecidable set, it is not very natural in the sense that it would not arise in practice. We next introduce one of the most naturally occuring examples of an undecidable set.

In the following result, fix any model computation you like, and fix some way of coding programs in that model as elements of HF. For example if you like python programs, you can code the symbols of python as natural numbers, and code a whole program as a finite sequence of natural numbers. Now some python programs halt, and others run forever. We let $H\subset HF$ consist of the set of codes for programs that halt.

**Theorem** The set $H$ of codes for halting programs is undecidable.

*Proof*. Let $A$ be a $\Sigma_1$ set which is not $\Delta_1$. Let $\phi$ be a $\Delta_0$-formula such that $x\in A$ if and only if $\exists y\phi(x,y)$. For each $x$ let $h_x$ be a code for the program which searches through all possible $y\in HF$ until it finds one such that $\phi(x,y)$. Then $x\in A$ if and only if $h_x\in H$. Thus if $H$ were $\Delta_1$ then so would $A$ be $\Delta_1$, a contradicton. $\blacksquare$

In this proof we defined a function $r\colon HF\to HF$ with the property that $x\in A\iff r(x)\in H$. Such a funcion is called a *reduction* from $A$ to $H$, and it implies that the complexity of $H$ is no simpler than that of $A$. If one wishes to prove that a given set is undecidable, the most common proof technique is to find a reduction from some known undecidable set to the given set.

### 10. Decidability in logic and incompleteness

In this section we apply our understanding of diagonalization and undecidability in the setting of logical proof. The result will be Godel's incompleteness theorems.

Recall that if $T$ is a theory then its deductive closure is the set $\bar T=\set{\sigma\mid T\vdash\sigma}$. Most theories that we have described are decidable, but the deductive closure may or may not be.

For example it is not difficult to decide whether or not a given sentence $\sigma$ is in ZFC, but it is much more decide whether $\sigma$ is a theorem of ZFC. OF course ZFC is very powerful, so this may not be too surprising. But we can study the same questions about deductive closure in the context of much simpler theories.

**Definition** Core set theory, or CST, is the theory consisting of the Axiom of Extensionality, Axiom of Pairing, Axiom of Union, Axiom of Comprehension, and the Axiom of Foundation.

This theory may seem weak compared to ZFC, but it is strong enough to do finite set theory plus induction. It is also possible to work Peano Arithmetic, the usual axioms of the natural numbers with $+,\cdot$ including the induction scheme.

**First incompleteness theorem** If $T$ is any consistent extension of CST then $\bar T$ is undecidable.

In our proof of the first incompleteness theorem, we once again return to a diagonalization argument. This time we will need to "represent" subsets of HF inside $T$ itself.

**Proposition** Every element $a\in HF$ is $\Delta_0$-definable. That is, there is a $\Delta_0$-formula $\delta_a(x)$ such that $x=a\iff\delta_a(x)$.

The propostion says that we don't need to add terms for elements of HF, we can already represent these elements in the language.

**Definition** Given a theory $T$ of $\in$, a formula $\phi$, and an element $a\in HF$, we will say that $T\vdash\phi(\langle a\rangle)$ if and only if $T\vdash\exists x\delta_a(x)\wedge\phi(x)$. CHECK

**Definition** Let $T$ be any theory of $\in$ and let $A\subset HF$. Then $A$ is *representable* in $T$ if there is a formula $\phi$ such that $a\in A$ if and only if $T\vdash\phi(\langle a\rangle)$.

**Proposition** Let $T$ be a consistent extension of CST. Then every $\Delta_0$-definable set is representable in $T$.

*Proof*. We will prove that for any $\Delta_0$-formula, we have $CST\vdash\phi(\langle a\rangle)$ if and only if $HF\models\phi[a]$. For atomic and negated atomic formulas $x\in y$, $x\notin y$, $x=y$, and $x\neq y$ are proved by induction on the rank of the elements $a,b$ that are plugged in for $x,y$. For general $\Delta_0$-formulas $\phi$ we use induction on the complexity of $\phi$. The boundedness of quantifiers is key because they reduce to conjuctions or disjunctions of atomics. $\blacksquare$

The claim that $CST\vdash\phi(\langle a\rangle)$ if and only if $HF\models\phi[a]$ fails for arbitrary formulas since for instance the negation of the Axiom of Infinity is true in HF but not provable from CST.

**Proposition** Let $T$ be a consistent extension of CST. Then every $\Delta_1$-definable set is representable in $T$.

*Proof*. Let $A$ be a $\Delta_1$-definable subset of HF, and let $\alpha,\beta$ be $\Delta_0$-formulas such that $a\in A$ iff $\exists y\alpha(a,y)$ iff $\forall z\beta(a,z)$. Note that we cannot use either of these two expressions directly to represent $A$, because they may be true without being witnessed in HF (that is, they may be witnessed by nonstandard elements). Instead we let $\psi(x)$ be the formula:

$\exists y\left[\alpha(x,y)\wedge\forall z \mathrm{rk}(z)\lt \mathrm{rk}(y)\rightarrow\beta(x,z)\right]$

We claim that $a\in A\iff T\vdash\psi(\langle a\rangle)$. First assume that $a\in A$. Then there is $y\in HF$ with the desired property. Since the inner portion of the sentence is $\Delta_0$, the previous proposition implies $T$ proves $\psi(\langle a\rangle)$.

Conversely assume that $a\notin A$. We claim that $CST\vdash\neg\psi(\langle a\rangle)$, that is,

$\forall y\left[\neg\alpha(\langle a\rangle,y)\vee\exists z \mathrm{rk}(z)\lt \mathrm{rk}(y)\wedge\neg\beta(\langle a\rangle,z)\right]$

Indeed first find $z$ such that $CST\vdash\neg\beta(\langle a\rangle,\langle z\rangle)$. Next given any $y$, if $y\in HF$ then the first clause holds, and if not then the second clause holds. Now since $T$ is a consistent extension of CST, we conclude $T\not\vdash\psi(\langle a\rangle)$. $\blacksquare$

We are now ready to prove the final step of the first incompleteness theorem.

**Theorem** Suppose $T$ is a theory such that every $\Delta_1$-definable subset of HF is representable in $T$. Then $\bar T$ is undecidable.

*Proof*. Let $U=\set{(\phi,a)\mid T\vdash\phi(\langle a\rangle)}$. Then since every $\Delta_1$-definable set is representable in $T$, every $\Delta_1$-definable set  appears as a cross-section of $U$, namely $\set{a\mid (\phi,a)\in U}$. We say that $U$ is universal for $\Delta_1$ sets.

Now if $\bar T$ were decidable then $U$ would be decidable and hence $\Delta_1$-definable. Thus the diagonal set $D=\set{x\mid (x,x)\notin U}$ would be $\Delta_1$-definable. This is a contradiction because $D$ does not appear as a cross-section of $U$. $\blacksquare$

This completes the proof of the first incompleteness theorem. We can rephrase the first incompleteness theorem as follows.

**Corollary** If $T$ is any consistent, decidable extension of CST then $T$ is incomplete.

To see that this result follows from the first incompleteness theorem, note that if $T$ were complete then we would have $\bar T=T$.

The corollary is rather stunning, since it implies mathematicians will never know all truths about sets or arithmetic. We can't simply add axioms to ZFC (such as CH etc) to obtain a decidable theory which can prove or disprove all statements.

The corollary provides conditions under which there exists a sentence that is neither provable nor disprovable from $T$. However it does not provide an example of such a sentence $\sigma$. The second incompleteness theorem gives an explicit and relevant example of such a sentence $\sigma$.

**Second incompleteness theorem** If $T$ is any consistent, decidable extension of CST then, and $\sigma$ is the sentence which asserts that $T$ is consistent, then $T\not\vdash\sigma$.

*Proof idea*. It is possible to formalize consistency and provability in CST. It is further possible to construct a diagonal sentence $\tau$ which asserts in the formalization that "$T\not\vdash\tau$", that is, there is no proof from $T$ of $\tau$ itself. We omit the details—it is like the liar paradox statement "this sentence is false", but with truth replaced by provability. Then $T\vdash\tau$ implies $T\not\vdash\tau$ and vice versa. This is a contradiction! $\blacksquare$

