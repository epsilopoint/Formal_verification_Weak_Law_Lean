# Formal_verification_Weak_Law_Lean

Here I proposed Formal verification of Weak Law of Large Numbers which is one of the fundamental theorem in probability theory. 

### Weak Law of Large Number 

 Let $X_1, X_2, \dots, X_n$ be a pairwise independent and identically distributed random variables each of which has a finite mean $\mathcal{E}[X_k] = \mu < \infty$.
 
 Let $S_n$ be the linear sum of the n random variables $S_n=X_1+X_2+\dots+X_n$. Then
 
 $$
 \forall \varepsilon >0, \ \lim_{n\to \infty}\mathcal{P}\left[\left|\frac{S_n}{n}-\mu\right|\right]=0
 $$

Proof based on applying Chebyshev's inequality and available in the repository in LaTex form.


Warning: You need to set up Lean and Mathlib to be able to open the project. Here is the most important information you should know about:

https://leanprover-community.github.io/
