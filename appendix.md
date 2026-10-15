#### Why it's called compactness (Not assessable)

It is natural to ask how the compactness theorem gets its name. It turns out that the compactness theorem is related to compactness in analysis. Briefly we present some of the results which demonstrate this connection.

To begin, let $V$ be the set of all truth assignments $v$. If $\alpha$ is a well-formed formula, we let $V_\alpha=\set{v\in V\mid v\models\alpha}$. We can define a topology on $V$ by declaring that $V_\alpha$ is *closed* for all $\alpha$. Thus a general closed subset of $V$ is defined to be an intersection of any number of sets of the form $V_\alpha$.

Recall that a topological space is **compact** if the following holds: if $\mathcal F$ is a family of closed sets such that for all $A_1,\ldots A_n\in\mathcal F$ we have $A_1\cap\cdots\cap A_n\neq\emptyset$, then we have $\bigcap\mathcal F\neq\emptyset$. This definition is equivalent to the more commonly stated open subcover property, and for metric spaces it's equivalent to the convergent subsequences property.

**Theorem** $V$ is a compact topological space.

*Proof*: Let $\mathcal F$ be a family of closed subsets of $V$ with the property that for all $A_1,\ldots A_n\in\mathcal F$ we have $A_1\cap\cdots\cap A_n\neq\emptyset$.

For each $A\in\mathcal F$, let $\Sigma_A=\set{\alpha\mid(\forall v\in A)v\models\alpha}$. We invite the reader to check that $v\in A$ if and only if $v\models\Sigma_A$.

Let $\Sigma=\bigcup_{A\in\mathcal F}\Sigma_A$. We claim that $\Sigma$ is finitely consistent. Indeed if $\Sigma_0\subset\Sigma$ is finite, then there exist $A_1,\ldots,A_n\in\mathcal F$ such that $\Sigma_0\subset\Sigma_{A_1}\cup\cdots\cup\Sigma_{A_n}$. By our assumption about $\mathcal F$, there exists $v\in A_1\cap\cdots\cap A_n$. We then have $v\models\Sigma_{A_1}\cup\cdots\cup\Sigma_{A_n}$ and thus $v\models\Sigma_0$.

By the compactness theorem, $\Sigma$ is consistent, that is, there exists $v\in V$ such that $v\models\Sigma$. Then for all $A\in\mathcal F$ we have $v\models\Sigma_A$. It follows that $v\in\bigcap_{A\in\mathcal F}A$, completing the proof. $\blacksquare$

Conversely, the compactness of the topological space $V$ may be used to show that the compactness theorem is true. For this, assume $\Sigma$ is finitely consistent. Let $\mathcal F=\set{V_\alpha:\alpha\in\Sigma}$. Then the fact that $\Sigma$ is finitely consistent plus the compactness of $V$ implies that $\bigcap\mathcal F\neq\emptyset$. Letting $v\in\bigcap\mathcal F$, we have $v\models\Sigma$, so $\Sigma$ is consistent.

Thus there is a sense in which the propositional compactness theorem is *equivalent* to the compactness of $V$. We hope this helps shed some light on the reason the compactness theorem is so named.