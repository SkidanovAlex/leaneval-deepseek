import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiMass

/-!
# TASK (child): prove `Submission.Multi.Esup_mul_le` below with a complete proof.
Goal: E sup_{λ∈Λ} Σ_x WW(x)·λ(x) for WW ~ multinomial of size Kbig·N is ≤ Kbig times the
same for size N (Kbig := MSys.Kbig = 10^70 ≥ 1).  This is the multiset "Esup additivity" used
to convert the deep size-KN bound into the size-N expectation (paper eq. lower-e-W).

## Definitions (in this file / imported):  all in namespace Submission.Multi unless noted
lamSum lam S m := ∑ x : X, (m x : ℝ) * lam S x
supLam Λ lam m := max over Λ.image (lamSum lam S m), default 0 if empty
Esup M μ Λ lam := ∑ m ∈ msizeExact (X:=X) M, mass (X:=X) M μ m · supLam Λ lam m
(`Λ : Finset (X → ℕ)` is the finite index set of weight functions `lam S : X → ℝ`.)

## THEOREM
theorem Esup_mul_le {X : Type*} [Fintype X] (N : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ))
    (lam : (X → ℕ) → X → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hlam0 : ∀ S ∈ Λ, ∀ x, 0 ≤ lam S x) :
    Esup (X := X) (MSys.Kbig * N) μ Λ lam ≤ (MSys.Kbig : ℝ) * Esup (X := X) N μ Λ lam := by ...

## PROOF OUTLINE
Let K := MSys.Kbig.  Assume K ≥ 1 (norm_num; K = 10^70).
1. JOINT: define the product sample space of K blocks of size N:
     blockFin := (Finset.univ : Finset (Fin K)).pi (fun _ : Fin K => msizeExact (X:=X) N)
   (a Finset of functions t : Fin K → X → ℕ with t i ∈ msizeExact N for every i; use
   `Finset.pi`; every element satisfies ∀ i, sizeM (t i) = N — extract via Finset.mem_pi).
   E_joint := ∑ t ∈ blockFin, (∏ i : Fin K, mass (X:=X) N μ (t i)) · supLam Λ lam (sum of t)
   where sum of t := fun x => ∑ i : Fin K, t i x   (the pointwise-sum multiset).
2. (a) E_joint ≤ K · Esup N:
     - sup-subadditivity: for each t, supLam Λ lam (sum_i t i) ≤ ∑ i : Fin K,
       supLam Λ lam (t i).  Prove a general lemma
         supLam_subadd {m1 m2 : X → ℕ} : supLam Λ lam (addM m1 m2) ≤ supLam Λ lam m1 +
           supLam Λ lam m2
       [unfold supLam; both sides are max' over the finite image; prove via Finset.max'_le:
        for any S ∈ Λ: lamSum lam S (addM m1 m2) = lamSum lam S m1 + lamSum lam S m2
        (pointwise (m1 x + m2 x)·lam = ...; sum_add_distrib) ≤ supLam m1 + supLam m2 by
        le_mSup-style max'-lemmas: max'_le with max' ≤ max' + max'...; provide local lemmas
        for max' over image: le_max'_add_max' etc. or use the ≤ with a direct argument]; then
        iterate to get the sum over Fin K, and ∏/∑ exchange: use Finset.sum_le_sum over i or a
        sum over pi via Finset.sum_pi-style factorization.
     - marginalization: for a fixed i₀, ∑ over the OTHER blocks of ∏_{j} mass N μ (t j) =
       mass N μ (t i₀) · (∑ over others ∏_{j≠i₀} mass N μ (t j)): the inner factor equals
       ((∑x μx)^N)^(K−1) = 1^(K−1) = 1 by mass_sum_eq_pow and hμ1, applied K−1 times:
       prove a helper: for t0 ∈ msizeExact N,
         (∑ t ∈ blockFin with t i₀ = t0, ∏ i, mass N μ (t i)) = mass N μ t0
       via iterated sum over the pi-finset (Finset.sum_pi / Finset.sum_bij factorization) and
       mass_sum_eq_pow; then E_joint ≤ ∑_{i₀} (∑_{t0} mass t0 · supLam t0) = K·Esup N.
     SIMPLER IMPLEMENTATION of (a): instead of full factorization, note
       supLam (Σ_i t_i) ≤ Σ_i supLam (t_i); plug into E_joint: E_joint ≤ ∑ t, ∏_i mass_i · Σ_i
       sup_i = Σ_i (∑ t, ∏_j mass_j · supLam (t i)) and by symmetry/summation each i-term equals
       Esup N: for the i-th term, sum over all t: = ∑_{t0 ∈ msizeExact N} mass(t0)·supLam(t0) ·
         (∑ over other blocks ∏ mass) = Esup N · 1^{K−1}: implement by Finset.sum over pi via
         `Finset.sum_pi` (check exists: #check Finset.sum_pi) or by rewriting the double sum:
         ∑ t ∈ pi, ∏_j mass (t j) · supLam(t i) = ∑_{t0} mass(t0)·supLam(t0)·(∑ over the other
         coordinates ∏_{j≠i} mass) and the latter inner sum = (∑_{w ∈ msizeExact N} mass w)^(K−1)
         = 1^(K−1): prove an auxiliary lemma
           sum_others_pi (K) (i₀ : Fin K) (g : (Fin K → X → ℕ) → ℝ) ...  — you may find it
           cleaner to instead PROVE a general "product measure on pi factors" lemma:
           ∑ t ∈ Finset.univ.pi (fun _ => msizeExact N), ∏ i, f (t i) = (∑ w ∈ msizeExact N,
           f w) ^ K   [for f : (X→ℕ) → ℝ; Finset.pi products factorize; prove by induction on
           K or by Finset.sum_pi if available; search `#check Finset.sum_pi`,
           `#check Finset.prod_pi`, `#check Finset.mem_pi`].
         Then the i-th term = (∑ w mass w · supLam w) · (∑w mass w)^{K−1} = Esup N · 1^{K−1}.
   (b) E_joint = Esup (K·N):  the map t ↦ (fun x => ∑ i, t i x) sends the product-of-mass-N
       measure onto the mass-(K·N) measure: for each W ∈ msizeExact (K·N):
         (∑ t ∈ pi with Σ_i t i = W, ∏ i, mass N μ (t i)) = mass (K·N) μ W
       PROVE by induction on K (or K−1 downward) using the two-block convolution:
         ∑_{a ∈ msizeExact N, b ∈ msizeExact (k N), a + b = W} mass N μ a · mass (k N) μ b
         = mass ((k+1) N) μ W
       [proof: unfold masses; reorganize: for fixed W of size (k+1)N, a ranges over sub-
        multisets of W of size N (b := subMM W a is then of size kN): the sum over a ⊆ W,
        sizeM a = N of mass N a · mass kN (W−a): use mass_mul-style algebra: mass N μ a ·
        mass (k N) μ (subMM W a) = mass((k+1)N) μ W · (choose-weight per x: Π_x C(Wx,ax)-ish
        times factorials) — derive from Submission/MultiZ.lean mass_mul_cost_eq with c := 1 and
        t := N? NO (sizes differ per block): do it directly: write mass N μ a = N!·∏ μ^{ax}/ax!,
        mass (kN) μ (W−a) = (kN)!·∏ μ^{Wx−ax}/(Wx−ax)!; product = N!(kN)!·∏ μ^{Wx}/(ax!(Wx−ax)!) =
        mass((k+1)N) μ W · [N!(kN)!/((k+1)N)!] · ∏ C(Wx, ax)·((k+1)N)!/(N!(kN)!)...  cleaner:
        product = mass((k+1)N) μ W · (N!(kN)!)/((k+1)N)! · ∏_x (Wx.choose ax : ℝ)   [real;
        prove as a corollary-style lemma with the SAME per-x algebra as MultiZ.mass_mul_cost_eq,
        by induction-free unfolding; note the factorial ratio is a CONSTANT independent of a];
        then Σ over a ⊆ W size N of ∏_x (Wx.choose ax : ℝ) = ((sizeM W).choose N : ℝ)?? NO: by
        Vandermonde: Σ_{a ⊆ W, |a|=N} ∏_x C(Wx, ax) = C(|W|, N) = C((k+1)N, N) (choose N items
        from the multiset W's (k+1)N occurrences, grouped by color x): prove via the generating
        identity ∏_x (1+u)^{Wx} = (1+u)^{(k+1)N}: the coefficient of u^N: Σ over a (with
        |a|=N) ∏ C(Wx,ax) = C((k+1)N, N)  [polynomial/coefficient identity on (1+u)^m: prove by
        induction or by using the mathlib binomial theorem add_pow twice, or simply by showing
        both sides count... in Lean easiest: prove the combinatorial identity by induction on
        the number of coordinates via Finset.induction on X? — or use the explicit route:
        (1+u)^((k+1)N) = ∏_x (1+u)^{Wx} (prod_pow_eq_pow_sum) and expand each (1+u)^{Wx} by
        add_pow; coefficient extraction is painful — ALTERNATIVE: PROVE the whole convolution
        lemma by induction on the number of ELEMENTS via iterating mass_sum_eq_pow: define the
        map W ↦ Σ_{a⊆W,|a|=N}... hmm.]
       SIMPLER ROUTE for (b): E_joint ≤ K·Esup N is what we need as the ≤; for the = we need
       E_joint = Esup(KN).  INSTEAD of the per-W convolution, PROVE by induction on K with the
       additive property of the sup directly:
         Claim E_{M_{(k+1)N}}[v] ≤ E_{M_{kN}}[v] + E_{M_N}[v] for v := supLam Λ lam
       [true: a size-(k+1)N multiset = block of kN + block of N via the same convolution; needs
        the convolution per-W again...].  NO ESCAPE: we need the convolution identity at least
        in the following weak form: Σ over W ∈ msizeExact((k+1)N) of mass((k+1)N)μW·v(W) equals
        Σ over (a,b) blocks of ∏mass·v(a+b) — i.e. E_{M_{(k+1)N}}[v] = E_joint for two blocks.
        Hmm — maybe prove additivity DIFFERENTLY without blocks: E_{M_{M1+M2}}[v] ≤ E_{M_{M1}}[v]
        + E_{M_{M2}}[v] for M1,M2 via: consider W of size M1+M2 and pick a RANDOM sub-multiset
        of size M1... requires hypergeometric... no.
       RECOMMENDED approach that AVOIDS per-W convolution: bound the two sides by the JOINT in
       both directions via ≤-style arguments with SUP-SUBADDITIVITY only, using the identity
       that the sum over W of mass((k+1)N)μW·(any f W) equals the sum over (a,b) of massN·
       mass(kN)·f(a+b) — prove THIS identity directly by noting both sides equal the coefficient
       of the product ∏_x (Σ...)...  OK here is the cleanest finite proof: work with the
       generating product ∏_x e^{t·μx}-style is overkill.
       FINAL RECOMMENDATION: prove the exact convolution identity
         conv_two : Σ_{a ∈ msizeExact N} mass N μ a · mass (M2) μ (subMM W a) = mass (N+M2) μ W
       when sizeM W = N + M2 and W ranges... (sum only over a ⊆ W: others give 0 automatically
       since subMM W a has wrong size → mass with sizeM ≠ M2 is NOT zero automatically!  mass
       M2 μ m for m of wrong size is NOT 0.  So instead sum over a with sizeM a = N AND
       subM a W: encode by (msizeExact N).filter (subM a W)? still Fintype-free (it's a
       Finset filter) ✓.  Prove:
         (∑ a ∈ (msizeExact N).filter (fun a => subM a W), mass N μ a · mass M2 μ (subMM W a))
         = mass (N + M2) μ W   given sizeM W = N + M2
       via per-x algebra + the Vandermonde identity Σ_{a: Σax = N, ax ≤ Wx} ∏ C(Wx,ax) =
       C(N+M2, N) where the LHS counts choosing N of the N+M2 occurrences: prove the
       Vandermonde by induction on the Finset of coordinates or via the binomial theorem:
       ∏_x (1 + u)^{Wx} = (1+u)^{N+M2}: coefficient of u^N = C(N+M2,N): coefficient extraction
       from add_pow-expanded products... you may use `Finset.sum_pow`?  Try to find in Mathlib
       a ready theorem (search: `Nat.choose` identities, `add_pow`, `Finset.sum_pow`):
       if none fits, do the coefficient extraction manually with `add_pow` for each factor and
       Finset.sum over the exponents a x with Σ a x = N (filter sums over univ of exponents are
       bounded: encode exponent tuples as msizeExact? each a x ≤ W x ≤ N+M2: represent via
       (Finset.range (N+M2+1))-valued... use the SAME encoding trick as msizeExact: tuples
       (x ↦ exponent) with Σ = N: exactly msizeExact N FILTERED by ax ≤ Wx: reuse!).
       This is the hardest algebra of the file; take your time.
       THEN iterate conv_two for K blocks (induction on k: combine a block of size N with the
       accumulated (k N)) to get E_joint = Esup (K·N) (summing v over W with masses).
3. Combine (a) and (b): Esup (K·N) = E_joint ≤ K · Esup N.
   (You need Esup N ≥ 0 to... no, (b) is an equality and (a) a ≤; done.)

## PRAGMATIC NOTES
- supLam with Λ possibly empty: supLam of empty = 0; both sides 0 if Λ = ∅: handle separately
  or make sure lemmas hold (max' over empty default 0: prove supLam_le_of_forall / le_supLam as
  needed; mirror MSys.mSup lemmas in MultiDeep2.lean but over the Finset Λ).
- All sums/∏ are finite.  Factorizations over Fin K products: use Finset.pi; check
  `#check Finset.pi` / `#check Finset.mem_pi` / `#check Finset.sum_pi` / `#check Finset.prod_pi`
  and use them; if Finset.pi is awkward, replace Fin K with a Finset K' : Finset ℕ of size K
  (e.g. Finset.range K) and iterate with Finset induction on range K (induction on k : ℕ with
  k ≤ K) — MAY BE EASIER: do the whole additivity by INDUCTION on k := number of blocks,
  stating it as: Esup (k*N) ≤ (k:ℝ)·Esup N for all k ≥ 1, using conv_two (two-block exact
  convolution) plus the sup-subadditivity for two blocks at each step:
     Esup((k+1)N) = E_joint(blocks kN, N) ≤ Esup(kN) + Esup(N) ≤ (k+1)·Esup N.
   This avoids Fin K products entirely — ONLY the 2-block joint is needed:
     two-block joint := ∑_{a ∈ msizeExact N} ∑_{b ∈ msizeExact (k·N)} mass N a · mass (kN) b ·
       supLam Λ lam (addM a b): show = Esup ((k+1)·N) [conv_two summed with v] and
       ≤ Esup(kN) + Esup(N) [sup-subadd + marginals via mass_sum_eq_pow].  INDUCE on k.
  SO: main work = conv_two (exact 2-block convolution, with the Vandermonde coefficient step)
  and sup-subadditivity + marginals for the two-block joint.  Define K := MSys.Kbig and apply
  the induction lemma at k := K.

Keep imports as they are.  Namespace: Submission.Multi.  No sorries at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open MSys

variable {X : Type*} [Fintype X]

/-- sum over x of m x · lam S x -/
noncomputable def lamSum (lam : (X → ℕ) → X → ℝ) (S m : X → ℕ) : ℝ :=
  ∑ x : X, (m x : ℝ) * lam S x

/-- sup over Λ of lamSum -/
noncomputable def supLam (Λ : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ) (m : X → ℕ) : ℝ := by
  classical
  let l : Finset ℝ := Λ.image (fun S : X → ℕ => lamSum lam S m)
  exact if h : l.Nonempty then l.max' h else 0

/-- E sup over WW of size M -/
noncomputable def Esup (M : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ))
    (lam : (X → ℕ) → X → ℝ) : ℝ :=
  ∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m * supLam Λ lam m

/-! ## supLam basics -/

/-- lamSum is additive in the multiset argument -/
lemma lamSum_add (lam : (X → ℕ) → X → ℝ) (m1 m2 S : X → ℕ) :
    lamSum lam S (addM m1 m2) = lamSum lam S m1 + lamSum lam S m2 := by
  unfold lamSum addM
  calc
    (∑ x : X, ((m1 x + m2 x : ℕ) : ℝ) * lam S x)
        = ∑ x : X, ((m1 x : ℝ) * lam S x + (m2 x : ℝ) * lam S x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Nat.cast_add]
          ring
    _ = (∑ x : X, (m1 x : ℝ) * lam S x) + (∑ x : X, (m2 x : ℝ) * lam S x) := by
          rw [Finset.sum_add_distrib]

/-- lamSum of the zero multiset is zero -/
lemma lamSum_zero (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) :
    lamSum lam S (fun _ : X => 0) = 0 := by
  unfold lamSum
  simp

/-- every member value is ≤ the sup -/
lemma lamSum_le_supLam {Λ : Finset (X → ℕ)} {lam : (X → ℕ) → X → ℝ} {m : X → ℕ}
    {S : X → ℕ} (hS : S ∈ Λ) : lamSum lam S m ≤ supLam Λ lam m := by
  classical
  unfold supLam
  by_cases h : (Λ.image (fun S : X → ℕ => lamSum lam S m)).Nonempty
  · simp [h]
    exact Finset.le_max' (Λ.image (fun S : X → ℕ => lamSum lam S m)) (lamSum lam S m)
      (Finset.mem_image.mpr ⟨S, hS, rfl⟩)
  · exfalso
    exact h ⟨lamSum lam S m, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩

/-- sup is ≤ c when every member value is ≤ c (and c ≥ 0 for the empty case) -/
lemma supLam_le_of_forall {Λ : Finset (X → ℕ)} {lam : (X → ℕ) → X → ℝ} {m : X → ℕ} {c : ℝ}
    (hc : ∀ S ∈ Λ, lamSum lam S m ≤ c) (hc0 : 0 ≤ c) : supLam Λ lam m ≤ c := by
  classical
  unfold supLam
  by_cases h : (Λ.image (fun S : X → ℕ => lamSum lam S m)).Nonempty
  · simp [h]
    intro a ha
    exact hc a ha
  · have hΛ : Λ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hΛ'
      rcases hΛ' with ⟨S, hS⟩
      exact h ⟨lamSum lam S m, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
    simp [h, hΛ, hc0]

lemma supLam_nonneg {Λ : Finset (X → ℕ)} {lam : (X → ℕ) → X → ℝ} {m : X → ℕ}
    (hlam0 : ∀ S ∈ Λ, ∀ x, 0 ≤ lam S x) : 0 ≤ supLam Λ lam m := by
  classical
  by_cases hΛ : Λ.Nonempty
  · rcases hΛ with ⟨S, hS⟩
    have h0 : 0 ≤ lamSum lam S m := by
      unfold lamSum
      exact Finset.sum_nonneg (by intro x hx; exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (hlam0 S hS x))
    exact le_trans h0 (lamSum_le_supLam hS)
  · have hΛ' : Λ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hΛ
    unfold supLam
    simp [hΛ']

/-- sup of a sum of two multisets is ≤ the sum of the sups (subadditivity) -/
lemma supLam_subadd {Λ : Finset (X → ℕ)} {lam : (X → ℕ) → X → ℝ} (m1 m2 : X → ℕ) :
    supLam Λ lam (addM m1 m2) ≤ supLam Λ lam m1 + supLam Λ lam m2 := by
  classical
  by_cases hΛ : Λ.Nonempty
  · rcases hΛ with ⟨S0, hS0⟩
    unfold supLam
    by_cases hne_add : (Λ.image (fun S : X → ℕ => lamSum lam S (addM m1 m2))).Nonempty
    · by_cases hne1 : (Λ.image (fun S : X → ℕ => lamSum lam S m1)).Nonempty
      · by_cases hne2 : (Λ.image (fun S : X → ℕ => lamSum lam S m2)).Nonempty
        · simp [hne_add, hne1, hne2]
          intro a ha
          calc
            lamSum lam a (addM m1 m2) = lamSum lam a m1 + lamSum lam a m2 := lamSum_add lam m1 m2 a
            _ ≤ (Λ.image (fun S : X → ℕ => lamSum lam S m1)).max' hne1
                + (Λ.image (fun S : X → ℕ => lamSum lam S m2)).max' hne2 := by
                  exact add_le_add
                    (Finset.le_max' (Λ.image (fun S : X → ℕ => lamSum lam S m1)) (lamSum lam a m1)
                      (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
                    (Finset.le_max' (Λ.image (fun S : X → ℕ => lamSum lam S m2)) (lamSum lam a m2)
                      (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
        · exfalso
          exact hne2 ⟨lamSum lam S0 m2, Finset.mem_image.mpr ⟨S0, hS0, rfl⟩⟩
      · exfalso
        exact hne1 ⟨lamSum lam S0 m1, Finset.mem_image.mpr ⟨S0, hS0, rfl⟩⟩
    · exfalso
      exact hne_add ⟨lamSum lam S0 (addM m1 m2), Finset.mem_image.mpr ⟨S0, hS0, rfl⟩⟩
  · have hΛ' : Λ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hΛ
    unfold supLam
    simp [hΛ']

/-- supLam at the zero multiset is zero -/
lemma supLam_zero (Λ : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ) :
    supLam Λ lam (fun _ : X => 0) = 0 := by
  classical
  apply le_antisymm
  · exact supLam_le_of_forall (m := fun _ : X => 0) (fun S hS => by simp [lamSum_zero lam S]) le_rfl
  · by_cases hΛ : Λ.Nonempty
    · rcases hΛ with ⟨S, hS⟩
      have h0 : 0 ≤ lamSum lam S (fun _ : X => 0) := by simp [lamSum_zero lam S]
      exact le_trans h0 (lamSum_le_supLam (m := fun _ : X => 0) hS)
    · have hΛ' : Λ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hΛ
      unfold supLam
      simp [hΛ']

/-! ## The two-block convolution (exact multinomial splitting)

`FiberSum P Q μ W` is the sum over size-`P` sub-multisets `a` of `W` of
`mass P μ a · mass Q μ (W − a)`.  When `sizeM W = P + Q` this equals
`mass (P + Q) μ W`.  We prove it by induction on `P` using the erase-one
recursion of the multinomial mass (mirroring `MultiMass.mass_sum_eq_pow`).
-/

/-- exact-size-zero multisets form a singleton -/
lemma msizeExact_zero : msizeExact (X := X) 0 = ({fun _ : X => 0} : Finset (X → ℕ)) := by
  classical
  ext m
  rw [mem_msizeExact_iff (X := X) (m := m) (M := 0)]
  constructor
  · intro hm
    exact (Finset.mem_singleton).mpr (by
      funext x
      have hle : m x ≤ sizeM m :=
        Finset.single_le_sum (by intro y hy; exact Nat.zero_le _) (Finset.mem_univ x)
      omega)
  · intro hm
    have hEq : m = (fun _ : X => 0) := Finset.mem_singleton.mp hm
    rw [hEq]
    simp [sizeM]

/-- W − (addOne b y) = (eraseOne W y) − b  (truncated subtraction) -/
lemma subMM_addOne_eraseOne (W b : X → ℕ) (y : X) :
    subMM W (addOne b y) = subMM (eraseOne W y) b := by
  funext x
  unfold subMM addOne eraseOne
  by_cases hxy : x = y
  · subst x
    simp
    rw [Nat.sub_sub]
    omega
  · simp [hxy]

/-- size of a difference of multisets -/
lemma sizeM_subMM_eq {m m' : X → ℕ} (h : subM m m') : sizeM (subMM m' m) = sizeM m' - sizeM m := by
  have haddM : addM (subMM m' m) m = m' := by
    funext x
    unfold addM subMM
    exact Nat.sub_add_cancel (h x)
  have hs : sizeM (subMM m' m) + sizeM m = sizeM m' := by
    rw [← sizeM_add, haddM]
  omega

/-- the one-block convolution sum (no size constraint on W yet) -/
noncomputable def FiberSum (P Q : ℕ) (μ : X → ℝ) (W : X → ℕ) : ℝ :=
  ∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
    mass (X := X) P μ a * mass (X := X) Q μ (subMM W a)

/-- reindexing step of the induction: (a, y) with y in the support of a  ↔  (y, b) -/
lemma fiber_step_reindex (P Q : ℕ) (μ : X → ℝ) (W : X → ℕ) :
    (∑ a ∈ (msizeExact (X := X) (P + 1)).filter (fun a : X → ℕ => subM a W),
        ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ a y)),
          μ y * mass (X := X) P μ (eraseOne a y) * mass (X := X) Q μ (subMM W a))
      = (∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ W y)),
        ∑ b ∈ (msizeExact (X := X) P).filter (fun b : X → ℕ => subM b (eraseOne W y)),
          μ y * mass (X := X) P μ b * mass (X := X) Q μ (subMM (eraseOne W y) b)) := by
  classical
  let A : Finset (X → ℕ) := (msizeExact (X := X) (P + 1)).filter (fun a : X → ℕ => subM a W)
  let S : Finset (Sigma fun _ : X → ℕ => X) :=
    A.sigma (fun a : X → ℕ => Finset.univ.filter (fun y : X => 1 ≤ a y))
  let Y : Finset X := Finset.univ.filter (fun y : X => 1 ≤ W y)
  let T : Finset (Sigma fun _ : X => X → ℕ) :=
    Y.sigma (fun y : X => (msizeExact (X := X) P).filter (fun b : X → ℕ => subM b (eraseOne W y)))
  have hST :
      (∑ p ∈ S, μ p.2 * mass (X := X) P μ (eraseOne p.1 p.2) * mass (X := X) Q μ (subMM W p.1))
        = (∑ q ∈ T, μ q.1 * mass (X := X) P μ q.2 * mass (X := X) Q μ (subMM (eraseOne W q.1) q.2)) := by
    refine Finset.sum_bij (fun p hp => (⟨p.2, eraseOne p.1 p.2⟩ : Sigma (fun _ : X => X → ℕ))) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_sigma] at hp
      have hmemA : p.1 ∈ (msizeExact (X := X) (P + 1)).filter (fun a : X → ℕ => subM a W) := hp.1
      have hy : p.2 ∈ Finset.univ.filter (fun y : X => 1 ≤ p.1 y) := hp.2
      have hmemA' : p.1 ∈ msizeExact (X := X) (P + 1) := (Finset.mem_filter.mp hmemA).1
      have hsubA : subM p.1 W := (Finset.mem_filter.mp hmemA).2
      rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_filter]
        constructor
        · simp
        · exact le_trans (Finset.mem_filter.mp hy).2 (hsubA p.2)
      · rw [Finset.mem_filter]
        constructor
        · apply mem_msizeExact
          have hsz : sizeM p.1 = P + 1 :=
            (mem_msizeExact_iff (X := X) (m := p.1) (M := P + 1)).mp hmemA'
          have hpos : 0 < p.1 p.2 := (Finset.mem_filter.mp hy).2
          have hsz2 : sizeM (eraseOne p.1 p.2) = sizeM p.1 - 1 := sizeM_eraseOne p.1 p.2 hpos
          rw [hsz2, hsz]
          omega
        · intro x
          by_cases hxy : x = p.2
          · subst x
            have hle : p.1 p.2 ≤ W p.2 := hsubA p.2
            have hpos : 1 ≤ p.1 p.2 := (Finset.mem_filter.mp hy).2
            simp [eraseOne]
            omega
          · simp [eraseOne, hxy]
            exact hsubA x
    · intro p1 hp1 p2 hp2 heq
      rcases p1 with ⟨a1, y1⟩
      rcases p2 with ⟨a2, y2⟩
      have hyeq : y1 = y2 := congrArg Sigma.fst heq
      subst y2
      have he' : eraseOne a1 y1 = eraseOne a2 y1 := by
        simpa using congrArg Sigma.snd heq
      have hpos1 : 1 ≤ a1 y1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp1).2).2
      have hpos2 : 1 ≤ a2 y1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp2).2).2
      have ha : a1 = a2 := by
        calc
          a1 = addOne (eraseOne a1 y1) y1 := (eraseOne_addOne (m := a1) y1 hpos1).symm
          _ = addOne (eraseOne a2 y1) y1 := by rw [he']
          _ = a2 := eraseOne_addOne (m := a2) y1 hpos2
      subst a2
      rfl
    · intro q hq
      rcases q with ⟨y, b⟩
      have hyY : y ∈ Y := (Finset.mem_sigma.mp hq).1
      have hb : b ∈ (msizeExact (X := X) P).filter (fun b : X → ℕ => subM b (eraseOne W y)) :=
        (Finset.mem_sigma.mp hq).2
      have hb' : b ∈ msizeExact (X := X) P := (Finset.mem_filter.mp hb).1
      have hsubb : subM b (eraseOne W y) := (Finset.mem_filter.mp hb).2
      refine ⟨(⟨addOne b y, y⟩ : Sigma (fun _ : X → ℕ => X)), ?_, ?_⟩
      · rw [Finset.mem_sigma]
        constructor
        · rw [Finset.mem_filter]
          constructor
          · apply mem_msizeExact
            have hsz : sizeM b = P :=
              (mem_msizeExact_iff (X := X) (m := b) (M := P)).mp hb'
            change sizeM (addOne b y) = P + 1
            rw [sizeM_addOne, hsz]
          · intro x
            by_cases hxy : x = y
            · subst x
              have hyW : 1 ≤ W y := (Finset.mem_filter.mp hyY).2
              have hby : b y ≤ W y - 1 := by simpa [eraseOne] using hsubb y
              simp [addOne, eraseOne]
              omega
            · have hbw : b x ≤ W x := by simpa [eraseOne, hxy] using hsubb x
              simp [addOne, eraseOne, hxy]
              exact hbw
        · rw [Finset.mem_filter]
          constructor
          · simp
          · change 1 ≤ addOne b y y
            simp [addOne]
      · change (⟨y, eraseOne (addOne b y) y⟩ : Sigma (fun _ : X => X → ℕ)) = ⟨y, b⟩
        rw [addOne_eraseOne]
    · intro p hp
      rcases p with ⟨a, y⟩
      dsimp
      have hypos : 1 ≤ a y := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
      have ha : a = addOne (eraseOne a y) y := (eraseOne_addOne (m := a) y hypos).symm
      rw [ha]
      rw [addOne_eraseOne]
      rw [subMM_addOne_eraseOne W (eraseOne a y) y]
  calc
    (∑ a ∈ (msizeExact (X := X) (P + 1)).filter (fun a : X → ℕ => subM a W),
        ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ a y)),
          μ y * mass (X := X) P μ (eraseOne a y) * mass (X := X) Q μ (subMM W a))
        = (∑ p ∈ S, μ p.2 * mass (X := X) P μ (eraseOne p.1 p.2) * mass (X := X) Q μ (subMM W p.1)) := by
          dsimp [S, A]
          rw [Finset.sum_sigma]
    _ = (∑ q ∈ T, μ q.1 * mass (X := X) P μ q.2 * mass (X := X) Q μ (subMM (eraseOne W q.1) q.2)) := hST
    _ = (∑ y ∈ Y, ∑ b ∈ (msizeExact (X := X) P).filter (fun b : X → ℕ => subM b (eraseOne W y)),
          μ y * mass (X := X) P μ b * mass (X := X) Q μ (subMM (eraseOne W y) b)) := by
          dsimp [T, Y]
          rw [Finset.sum_sigma]

/-- induction step: split off one unit by a support coordinate -/
lemma fiber_succ_sum (P Q : ℕ) (μ : X → ℝ) (W : X → ℕ) :
    FiberSum (P + 1) Q μ W
      = ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ W y)),
          μ y * FiberSum P Q μ (eraseOne W y) := by
  classical
  calc
    FiberSum (P + 1) Q μ W
        = (∑ a ∈ (msizeExact (X := X) (P + 1)).filter (fun a : X → ℕ => subM a W),
            (∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ a y)),
                μ y * mass (X := X) P μ (eraseOne a y)) * mass (X := X) Q μ (subMM W a)) := by
            unfold FiberSum
            apply Finset.sum_congr rfl
            intro a ha
            have haex : a ∈ msizeExact (X := X) (P + 1) := (Finset.mem_filter.mp ha).1
            rw [← (inner_mass_sum (M := P) μ a haex)]
    _ = (∑ a ∈ (msizeExact (X := X) (P + 1)).filter (fun a : X → ℕ => subM a W),
            ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ a y)),
              μ y * mass (X := X) P μ (eraseOne a y) * mass (X := X) Q μ (subMM W a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_mul]
    _ = (∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ W y)),
            ∑ b ∈ (msizeExact (X := X) P).filter (fun b : X → ℕ => subM b (eraseOne W y)),
              μ y * mass (X := X) P μ b * mass (X := X) Q μ (subMM (eraseOne W y) b)) := by
            exact fiber_step_reindex P Q μ W
    _ = (∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ W y)),
            μ y * FiberSum P Q μ (eraseOne W y)) := by
            apply Finset.sum_congr rfl
            intro y hy
            unfold FiberSum
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            rw [mul_assoc]

/-- the two-block convolution identity -/
lemma fiber_eq_mass (P Q : ℕ) (μ : X → ℝ) (W : X → ℕ) (hW : sizeM W = P + Q) :
    FiberSum P Q μ W = mass (X := X) (P + Q) μ W := by
  classical
  revert hW
  revert W
  induction P with
  | zero =>
      intro W hW
      have hz : (msizeExact (X := X) 0).filter (fun a : X → ℕ => subM a W) =
          ({fun _ : X => 0} : Finset (X → ℕ)) := by
        rw [msizeExact_zero]
        rw [Finset.filter_singleton]
        simp [subM]
      unfold FiberSum
      rw [hz]
      simp [mass]
      have hsub : subMM W (fun _ : X => 0) = W := by
        funext x
        simp [subMM]
      rw [hsub]
      simp
  | succ P ih =>
      intro W hW
      have hs : 1 ≤ sizeM W := by
        rw [hW]
        omega
      rcases (sizeM_pos_iff.mp hs) with ⟨y, hypos⟩
      have hy1 : 1 ≤ W y := hypos
      have hWy : sizeM (eraseOne W y) = P + Q := by
        have hsz : sizeM (eraseOne W y) = sizeM W - 1 := sizeM_eraseOne W y hypos
        rw [hsz, hW]
        omega
      calc
        FiberSum (P + 1) Q μ W
            = ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ W y)),
                μ y * FiberSum P Q μ (eraseOne W y) := fiber_succ_sum P Q μ W
        _ = ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ W y)),
                μ y * mass (X := X) (P + Q) μ (eraseOne W y) := by
                apply Finset.sum_congr rfl
                intro y0 hy0
                congr 1
                exact ih (eraseOne W y0) (by
                  have hsz : sizeM (eraseOne W y0) = sizeM W - 1 :=
                    sizeM_eraseOne W y0 (Finset.mem_filter.mp hy0).2
                  rw [hsz, hW]
                  omega)
        _ = mass (X := X) ((P + Q) + 1) μ W := by
                rw [inner_mass_sum (M := P + Q) μ W]
                · apply mem_msizeExact
                  rw [hW]
                  omega
        _ = mass (X := X) ((P + 1) + Q) μ W := by
                congr 1
                omega

/-- reindex (a,b) pairs  ↔  (W, a ⊆ W) pairs, for the two-block joint -/
lemma pair_sum_eq_W_sum (P Q : ℕ) (μ : X → ℝ) (v : (X → ℕ) → ℝ) :
    (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
        mass (X := X) P μ a * mass (X := X) Q μ b * v (addM a b))
      = (∑ W ∈ msizeExact (X := X) (P + Q),
          ∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
            mass (X := X) P μ a * mass (X := X) Q μ (subMM W a) * v W) := by
  classical
  let A : Finset (X → ℕ) := msizeExact (X := X) P
  let B : Finset (X → ℕ) := msizeExact (X := X) Q
  let C : Finset (X → ℕ) := msizeExact (X := X) (P + Q)
  let T : Finset (Sigma fun _ : X → ℕ => X → ℕ) :=
    C.sigma (fun W : X → ℕ => (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W))
  have hST :
      (∑ p ∈ A.product B, mass (X := X) P μ p.1 * mass (X := X) Q μ p.2 * v (addM p.1 p.2))
        = (∑ q ∈ T, mass (X := X) P μ q.2 * mass (X := X) Q μ (subMM q.1 q.2) * v q.1) := by
    refine Finset.sum_bij (fun p hp => (⟨addM p.1 p.2, p.1⟩ : Sigma (fun _ : X → ℕ => X → ℕ))) ?_ ?_ ?_ ?_
    · intro p hp
      have ha : p.1 ∈ msizeExact (X := X) P := (Finset.mem_product.mp hp).1
      have hb : p.2 ∈ msizeExact (X := X) Q := (Finset.mem_product.mp hp).2
      rw [Finset.mem_sigma]
      constructor
      · apply mem_msizeExact
        have hsa : sizeM p.1 = P := (mem_msizeExact_iff (X := X) (m := p.1) (M := P)).mp ha
        have hsb : sizeM p.2 = Q := (mem_msizeExact_iff (X := X) (m := p.2) (M := Q)).mp hb
        change sizeM (addM p.1 p.2) = P + Q
        rw [sizeM_add, hsa, hsb]
      · rw [Finset.mem_filter]
        constructor
        · exact ha
        · intro x
          unfold addM
          exact Nat.le_add_right (p.1 x) (p.2 x)
    · intro p1 hp1 p2 hp2 heq
      rcases p1 with ⟨a1, b1⟩
      rcases p2 with ⟨a2, b2⟩
      have hW : addM a1 b1 = addM a2 b2 := congrArg Sigma.fst heq
      have ha : a1 = a2 := congrArg Sigma.snd heq
      subst a2
      have hb : b1 = b2 := by
        funext x
        have hx := congrFun hW x
        unfold addM at hx
        omega
      subst b2
      rfl
    · intro q hq
      rcases q with ⟨W, a⟩
      have hWmem : W ∈ msizeExact (X := X) (P + Q) := (Finset.mem_sigma.mp hq).1
      have hamem : a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W) :=
        (Finset.mem_sigma.mp hq).2
      have ha : a ∈ msizeExact (X := X) P := (Finset.mem_filter.mp hamem).1
      have hsub : subM a W := (Finset.mem_filter.mp hamem).2
      refine ⟨(⟨a, subMM W a⟩ : (X → ℕ) × (X → ℕ)), ?mem, ?eq⟩
      · dsimp [A, B]
        rw [Finset.mem_product]
        constructor
        · exact ha
        · apply mem_msizeExact
          have hsW : sizeM W = P + Q := (mem_msizeExact_iff (X := X) (m := W) (M := P + Q)).mp hWmem
          have hsa : sizeM a = P := (mem_msizeExact_iff (X := X) (m := a) (M := P)).mp ha
          rw [sizeM_subMM_eq hsub, hsW, hsa]
          omega
      · change (⟨addM a (subMM W a), a⟩ : Sigma (fun _ : X → ℕ => X → ℕ)) = ⟨W, a⟩
        rw [addM_subMM_cancel hsub]
    · intro p hp
      rcases p with ⟨a, b⟩
      dsimp
      have hsub : subMM (addM a b) a = b := by
        funext x
        unfold subMM addM
        exact Nat.add_sub_cancel_left (a x) (b x)
      rw [hsub]
  calc
    (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
        mass (X := X) P μ a * mass (X := X) Q μ b * v (addM a b))
        = (∑ p ∈ A.product B, mass (X := X) P μ p.1 * mass (X := X) Q μ p.2 * v (addM p.1 p.2)) := by
            dsimp [A, B]
            rw [Finset.sum_product]
    _ = (∑ q ∈ T, mass (X := X) P μ q.2 * mass (X := X) Q μ (subMM q.1 q.2) * v q.1) := hST
    _ = (∑ W ∈ msizeExact (X := X) (P + Q),
            ∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
              mass (X := X) P μ a * mass (X := X) Q μ (subMM W a) * v W) := by
            dsimp [T, C]
            rw [Finset.sum_sigma]

/-- the two-block joint equals the expectation at size P+Q -/
lemma joint_eq_Esup (P Q : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ) :
    (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
        mass (X := X) P μ a * mass (X := X) Q μ b * supLam Λ lam (addM a b))
      = Esup (X := X) (P + Q) μ Λ lam := by
  classical
  unfold Esup
  rw [pair_sum_eq_W_sum P Q μ (supLam Λ lam)]
  apply Finset.sum_congr rfl
  intro W hW
  have hsz : sizeM W = P + Q := (mem_msizeExact_iff (X := X) (m := W) (M := P + Q)).mp hW
  calc
    (∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
        mass (X := X) P μ a * mass (X := X) Q μ (subMM W a) * supLam Λ lam W)
        = (∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
            mass (X := X) P μ a * mass (X := X) Q μ (subMM W a)) * supLam Λ lam W := by
            rw [← Finset.sum_mul]
    _ = mass (X := X) (P + Q) μ W * supLam Λ lam W := by
            change FiberSum P Q μ W * supLam Λ lam W = mass (X := X) (P + Q) μ W * supLam Λ lam W
            rw [fiber_eq_mass P Q μ W hsz]

/-- Esup is subadditive in the size: Esup(P+Q) ≤ Esup P + Esup Q -/
lemma Esup_add_le (P Q : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1) :
    Esup (X := X) (P + Q) μ Λ lam ≤ Esup (X := X) P μ Λ lam + Esup (X := X) Q μ Λ lam := by
  classical
  rw [← joint_eq_Esup P Q μ Λ lam]
  calc
    (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
        mass (X := X) P μ a * mass (X := X) Q μ b * supLam Λ lam (addM a b))
        ≤ (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
            mass (X := X) P μ a * mass (X := X) Q μ b * (supLam Λ lam a + supLam Λ lam b)) := by
            apply Finset.sum_le_sum
            intro a ha
            apply Finset.sum_le_sum
            intro b hb
            have hm : 0 ≤ mass (X := X) P μ a * mass (X := X) Q μ b :=
              mul_nonneg (mass_nonneg P hμ0 a) (mass_nonneg Q hμ0 b)
            exact mul_le_mul_of_nonneg_left (supLam_subadd (Λ := Λ) (lam := lam) a b) hm
    _ = Esup (X := X) P μ Λ lam + Esup (X := X) Q μ Λ lam := by
            have hsumP : (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b) = 1 := by
              rw [mass_sum_eq_pow Q μ, hμ1]
              simp
            have hsumQ : (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a) = 1 := by
              rw [mass_sum_eq_pow P μ, hμ1]
              simp
            let va : (X → ℕ) → ℝ := fun m => supLam Λ lam m
            have h1 :
                (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                    mass (X := X) P μ a * mass (X := X) Q μ b * (va a + va b))
                  = (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                    + (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va b) := by
                    simp [mul_add, Finset.sum_add_distrib]
            have h2 :
                (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                    mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                  = ∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * va a := by
                calc
                  (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                      mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                      = ∑ a ∈ msizeExact (X := X) P,
                          (mass (X := X) P μ a * va a) * (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b) := by
                          apply Finset.sum_congr rfl
                          intro a ha
                          calc
                            (∑ b ∈ msizeExact (X := X) Q,
                                mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                                = ∑ b ∈ msizeExact (X := X) Q, (mass (X := X) P μ a * va a) * mass (X := X) Q μ b := by
                                    apply Finset.sum_congr rfl
                                    intro b hb
                                    ring
                            _ = (mass (X := X) P μ a * va a) * (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b) := by
                                    rw [Finset.mul_sum]
                      _ = ∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * va a := by
                            rw [hsumP]
                            simp
            have h3 :
                (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                    mass (X := X) P μ a * mass (X := X) Q μ b * va b)
                  = ∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * va b := by
                calc
                  (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                      mass (X := X) P μ a * mass (X := X) Q μ b * va b)
                      = ∑ b ∈ msizeExact (X := X) Q,
                          (mass (X := X) Q μ b * va b) * (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a) := by
                          rw [Finset.sum_comm]
                          apply Finset.sum_congr rfl
                          intro b hb
                          calc
                            (∑ a ∈ msizeExact (X := X) P,
                                mass (X := X) P μ a * mass (X := X) Q μ b * va b)
                                = ∑ a ∈ msizeExact (X := X) P, (mass (X := X) Q μ b * va b) * mass (X := X) P μ a := by
                                    apply Finset.sum_congr rfl
                                    intro a ha
                                    ring
                            _ = (mass (X := X) Q μ b * va b) * (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a) := by
                                    rw [Finset.mul_sum]
                      _ = ∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * va b := by
                            rw [hsumQ]
                            simp
            calc
              (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                  mass (X := X) P μ a * mass (X := X) Q μ b * (supLam Λ lam a + supLam Λ lam b))
                  = (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * (va a + va b)) := rfl
              _ = (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                    + (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va b) := h1
              _ = (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * va a)
                    + (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * va b) := by
                    rw [h2, h3]
              _ = Esup (X := X) P μ Λ lam + Esup (X := X) Q μ Λ lam := by
                    unfold Esup va
                    rfl

theorem conv_two (k N : ℕ) (μ : X → ℝ) (W : X → ℕ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hW : sizeM W = (k * N) + N) :
    (∑ a ∈ (msizeExact (X := X) N).filter (fun a : X → ℕ => subM a W),
        mass (X := X) N μ a * mass (X := X) (k * N) μ (subMM W a))
      = mass (X := X) ((k * N) + N) μ W := by
  classical
  have hW' : sizeM W = N + k * N := by
    rw [hW]
    omega
  have hfib := fiber_eq_mass N (k * N) μ W hW'
  -- hfib : FiberSum N (k*N) μ W = mass (N + k*N) μ W
  unfold FiberSum at hfib
  have hidx : (k * N) + N = N + k * N := by omega
  rw [hidx]
  rw [← hfib]

/-- Esup(k·N) ≤ k · Esup N for every k (used with k = Kbig) -/
lemma Esup_nat_mul_le (k N : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1) :
    Esup (X := X) (k * N) μ Λ lam ≤ (k : ℝ) * Esup (X := X) N μ Λ lam := by
  classical
  induction k with
  | zero =>
      have hz : Esup (X := X) 0 μ Λ lam = 0 := by
        unfold Esup
        rw [msizeExact_zero]
        simp [supLam_zero]
      simpa [hz] using (le_refl (0 : ℝ))
  | succ k ih =>
      calc
        Esup (X := X) ((k + 1) * N) μ Λ lam
            = Esup (X := X) (k * N + N) μ Λ lam := by
                have hidx : (k + 1) * N = k * N + N := by ring
                rw [hidx]
        _ ≤ Esup (X := X) (k * N) μ Λ lam + Esup (X := X) N μ Λ lam :=
                Esup_add_le (k * N) N μ Λ lam hμ0 hμ1
        _ ≤ (k : ℝ) * Esup (X := X) N μ Λ lam + (1 : ℝ) * Esup (X := X) N μ Λ lam := by
                exact add_le_add ih (by simp)
        _ = ((k + 1 : ℕ) : ℝ) * Esup (X := X) N μ Λ lam := by
                rw [Nat.cast_add]
                ring

theorem Esup_mul_le (N : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ))
    (lam : (X → ℕ) → X → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hlam0 : ∀ S ∈ Λ, ∀ x, 0 ≤ lam S x) :
    Esup (X := X) (Kbig * N) μ Λ lam ≤ (Kbig : ℝ) * Esup (X := X) N μ Λ lam := by
  classical
  exact Esup_nat_mul_le Kbig N μ Λ lam hμ0 hμ1
end Multi
end Submission
