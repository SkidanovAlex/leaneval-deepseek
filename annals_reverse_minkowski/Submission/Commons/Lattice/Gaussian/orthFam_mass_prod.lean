import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Lattice.Discrete.discreteTopology_of_le
import Submission.Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq

open scoped BigOperators

set_option maxHeartbeats 0
set_option linter.style.haveILetI false

namespace Commons.Lattice.Gaussian

/-! Helpers for the finite-product rule for Gaussian masses over orthogonal
internal direct sums of lattices. -/

/-- Sup over `Fin (m+1)` splits into the sup over the first `m` pieces plus the last. -/
lemma iSup_fin_last {m : ℕ} {α : Type*} [CompleteLattice α] (f : Fin (m + 1) → α) :
    (⨆ i : Fin (m + 1), f i) = (⨆ i : Fin m, f i.castSucc) ⊔ f (Fin.last m) := by
  apply le_antisymm
  · apply iSup_le_iff.mpr
    intro i
    by_cases hi : i = Fin.last m
    · rw [hi]
      exact le_sup_right
    · rcases (Fin.exists_castSucc_eq.mpr hi) with ⟨j, rfl⟩
      exact le_trans (le_iSup (fun j : Fin m => f j.castSucc) j) le_sup_left
  · apply sup_le
    · apply iSup_le_iff.mpr
      intro j
      exact le_iSup (fun i : Fin (m + 1) => f i) j.castSucc
    · exact le_iSup (fun i : Fin (m + 1) => f i) (Fin.last m)

section Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian mass term `exp (-π‖x‖²/s²)` (argument on the ambient space). -/
noncomputable def gm (s : ℝ) (x : E) : ℝ := Real.exp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)

/-- Elementwise-orthogonal submodules intersect only in `0`. -/
lemma orth_inf_eq_zero (A B : Submodule ℤ E)
    (horth : ∀ x : E, x ∈ A → ∀ y : E, y ∈ B → inner ℝ x y = 0) :
    ∀ x : E, x ∈ A → x ∈ B → x = 0 := by
  intro x hxA hxB
  exact (inner_self_eq_zero.mp (horth x hxA x hxB))

/-- Addition map from the product of two submodules into their sum. -/
def addMap (A B : Submodule ℤ E) : A × B → (A ⊔ B : Submodule ℤ E) := fun p =>
  ⟨p.1.1 + p.2.1, by
    exact Submodule.add_mem (A ⊔ B) (Submodule.mem_sup_left p.1.2)
      (Submodule.mem_sup_right p.2.2)⟩

/-- For elementwise-orthogonal submodules, addition is a bijection `A × B ≃ A ⊔ B`. -/
noncomputable def addEquiv (A B : Submodule ℤ E)
    (horth : ∀ x : E, x ∈ A → ∀ y : E, y ∈ B → inner ℝ x y = 0) : A × B ≃ (A ⊔ B : Submodule ℤ E) := by
  refine Equiv.ofBijective (addMap A B) ?_
  constructor
  · intro p q hpq
    have hval : p.1.1 + p.2.1 = q.1.1 + q.2.1 := by
      simpa [addMap] using congrArg Subtype.val hpq
    have h1 : p.1.1 - q.1.1 = q.2.1 - p.2.1 := by
      calc
        p.1.1 - q.1.1 = (p.1.1 + p.2.1) - (q.1.1 + p.2.1) := by abel
        _ = (q.1.1 + q.2.1) - (q.1.1 + p.2.1) := by rw [hval]
        _ = q.2.1 - p.2.1 := by abel
    have hdA : p.1.1 - q.1.1 ∈ A := Submodule.sub_mem A p.1.2 q.1.2
    have hdB : p.1.1 - q.1.1 ∈ B := by
      rw [h1]
      exact Submodule.sub_mem B q.2.2 p.2.2
    have hd0 : p.1.1 - q.1.1 = 0 := orth_inf_eq_zero A B horth (p.1.1 - q.1.1) hdA hdB
    have hp : p.1.1 = q.1.1 := sub_eq_zero.mp hd0
    have hq : p.2.1 = q.2.1 := by
      have hq' : q.2.1 - p.2.1 = 0 := h1.symm.trans hd0
      exact (sub_eq_zero.mp hq').symm
    exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)
  · intro z
    rcases (Submodule.mem_sup.mp z.2) with ⟨x, hxA, y, hyB, hxy⟩
    refine ⟨(⟨x, hxA⟩, ⟨y, hyB⟩), ?_⟩
    apply Subtype.ext
    exact hxy

/-- Orthogonality (Pythagoras) factorizes the Gaussian mass term on a sum. -/
lemma factor_add {s : ℝ} (hs : 0 < s) (A B : Submodule ℤ E)
    (horth : ∀ x : E, x ∈ A → ∀ y : E, y ∈ B → inner ℝ x y = 0) :
    ∀ p : A × B, gm s ((p.1 : E) + (p.2 : E)) = gm s (p.1 : E) * gm s (p.2 : E) := by
  intro p
  have horth12 : inner ℝ (p.1 : E) (p.2 : E) = 0 := horth (p.1 : E) p.1.2 (p.2 : E) p.2.2
  have hsq : ‖(p.1 : E) + (p.2 : E)‖ ^ 2 = ‖(p.1 : E)‖ ^ 2 + ‖(p.2 : E)‖ ^ 2 := by
    rw [norm_add_sq_real]
    rw [horth12]
    ring
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs)
  unfold gm
  rw [← Real.exp_add]
  congr 1
  rw [hsq]
  field_simp [hs2]
  ring

/-- The two-piece finite-product rule for Gaussian masses. -/
lemma two_piece_sum {s : ℝ} (hs : 0 < s) (A B : Submodule ℤ E)
    (horth : ∀ x : E, x ∈ A → ∀ y : E, y ∈ B → inner ℝ x y = 0)
    (hsumAB : Summable (fun z : (A ⊔ B : Submodule ℤ E) => gm s (z : E)))
    (hsumA : Summable (fun x : A => gm s (x : E)))
    (hsumB : Summable (fun y : B => gm s (y : E))) :
    (∑' z : (A ⊔ B : Submodule ℤ E), gm s (z : E)) =
      (∑' x : A, gm s (x : E)) * (∑' y : B, gm s (y : E)) := by
  let e : A × B ≃ (A ⊔ B : Submodule ℤ E) := addEquiv A B horth
  have hfactor : ∀ p : A × B, gm s ((e p : (A ⊔ B : Submodule ℤ E)) : E) =
      gm s (p.1 : E) * gm s (p.2 : E) := by
    intro p
    have hf := factor_add hs A B horth p
    have hcast : ((e p : (A ⊔ B : Submodule ℤ E)) : E) = (p.1 : E) + (p.2 : E) := by
      change ((addMap A B p : (A ⊔ B : Submodule ℤ E)) : E) = (p.1 : E) + (p.2 : E)
      rfl
    rw [hcast]
    exact hf
  have hsumRaw : Summable (fun p : A × B => gm s ((e p : (A ⊔ B : Submodule ℤ E)) : E)) := by
    exact (e.summable_iff).mpr hsumAB
  have hsumPair : Summable (fun p : A × B => gm s (p.1 : E) * gm s (p.2 : E)) := by
    exact hsumRaw.congr hfactor
  have hAB := HasSum.mul hsumA.hasSum hsumB.hasSum hsumPair
  calc
    (∑' z : (A ⊔ B : Submodule ℤ E), gm s (z : E))
        = ∑' p : A × B, gm s ((e p : (A ⊔ B : Submodule ℤ E)) : E) := by
          exact (Equiv.tsum_eq e (fun z : (A ⊔ B : Submodule ℤ E) => gm s (z : E))).symm
    _ = ∑' p : A × B, gm s (p.1 : E) * gm s (p.2 : E) := by
          exact tsum_congr hfactor
    _ = (∑' x : A, gm s (x : E)) * (∑' y : B, gm s (y : E)) := by
          exact hAB.tsum_eq

end Gauss

/-- Summability of the Gaussian mass over a discrete `ℤ`-lattice in a Euclidean space. -/
lemma summable_gm_Euclid {n : ℕ} (s : ℝ) (hs : 0 < s)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] :
    Summable (fun y : L => gm s (y : EuclideanSpace ℝ (Fin n))) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hsq : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs)
  have hc : 0 < Real.pi / s ^ 2 := by positivity
  have hsumb : Summable (fun y : L => Real.exp (-(Real.pi / s ^ 2) * ‖(y : E)‖ ^ 2)) := by
    exact Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq (E := E) (L := L)
      (c := Real.pi / s ^ 2) hc
  convert hsumb using 1
  funext y
  unfold gm
  congr 1
  field_simp [hsq]

/-- Finite-product rule for Gaussian masses over an internal direct sum of pairwise
elementwise-orthogonal lattices (worked in terms of the mass term `gm`). -/
private theorem massProdInd (n : ℕ) : ∀ (k : ℕ)
    (W : Fin k → Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (S : Submodule ℤ (EuclideanSpace ℝ (Fin n))),
    S = ⨆ i : Fin k, W i →
    (∀ i j : Fin k, i ≠ j → ∀ x : EuclideanSpace ℝ (Fin n), x ∈ W i →
      ∀ y : EuclideanSpace ℝ (Fin n), y ∈ W j → inner ℝ x y = 0) →
    (∀ i : Fin k, DiscreteTopology (W i)) →
    (s : ℝ) → 0 < s → [DiscreteTopology S] →
    (∑' z : S, gm s (z : EuclideanSpace ℝ (Fin n))) =
      ∏ i : Fin k, (∑' y : W i, gm s (y : EuclideanSpace ℝ (Fin n))) := by
  classical
  intro k
  induction k with
  | zero =>
      intro W S hS horth hdisc s hs _discS
      let E := EuclideanSpace ℝ (Fin n)
      have hz0 : ∀ z : S, (z : E) = 0 := by
        intro z
        have hzSup : (z : E) ∈ ⨆ i : Fin 0, W i := by
          simpa [hS] using z.2
        rw [iSup_of_empty (fun i : Fin 0 => W i)] at hzSup
        exact (Submodule.mem_bot ℤ).mp hzSup
      calc
        (∑' z : S, gm s (z : E)) = gm s ((0 : S) : E) := by
          refine tsum_eq_single (b := (0 : S)) (f := fun z : S => gm s (z : E)) ?_
          intro z hz
          exact (hz (Subtype.ext (hz0 z))).elim
        _ = ∏ i : Fin 0, (∑' y : W i, gm s (y : E)) := by
          simp [gm]
  | succ m ih =>
      intro W S hS horth hdisc s hs _discS
      let E := EuclideanSpace ℝ (Fin n)
      change (∑' z : S, gm s (z : E)) = ∏ i : Fin (m + 1), (∑' y : W i, gm s (y : E))
      let Wp : Fin m → Submodule ℤ E := fun i => W i.castSucc
      let P' : Submodule ℤ E := ⨆ i : Fin m, Wp i
      let B : Submodule ℤ E := W (Fin.last m)
      have hSsup : S = P' ⊔ B := by
        rw [hS]
        simpa [Wp, P', B] using (iSup_fin_last W)
      -- prefix ≤ S, last ≤ S
      have hPleS : P' ≤ S := by
        dsimp [P', Wp]
        rw [hS]
        exact (iSup_le_iff.mpr (fun i : Fin m => le_iSup (fun j : Fin (m + 1) => W j) i.castSucc))
      have hBleS : B ≤ S := by
        dsimp [B]
        rw [hS]
        exact le_iSup (fun j : Fin (m + 1) => W j) (Fin.last m)
      have hSupBleS : (P' ⊔ B : Submodule ℤ E) ≤ S := sup_le hPleS hBleS
      letI : DiscreteTopology (P' ⊔ B : Submodule ℤ E) := Commons.Lattice.Discrete.discreteTopology_of_le (ℒ := S) (ℒ' := (P' ⊔ B : Submodule ℤ E)) hSupBleS
      letI : DiscreteTopology P' := Commons.Lattice.Discrete.discreteTopology_of_le (ℒ := S) (ℒ' := P') hPleS
      -- orthogonality hypotheses for the prefix and between prefix and last
      have horthP' : ∀ i j : Fin m, i ≠ j → ∀ x : E, x ∈ Wp i →
          ∀ y : E, y ∈ Wp j → inner ℝ x y = 0 := by
        intro i j hij x hx y hy
        exact horth i.castSucc j.castSucc (fun hc => hij (Fin.castSucc_inj.mp hc)) x hx y hy
      have horthPB : ∀ x : E, x ∈ P' → ∀ y : E, y ∈ B → inner ℝ x y = 0 := by
        intro x hx y hy
        dsimp [B] at hy ⊢
        have hx' : x ∈ ⨆ i : Fin m, W i.castSucc := by simpa [Wp, P'] using hx
        refine Submodule.iSup_induction (p := fun i : Fin m => W i.castSucc)
          (motive := fun v : E => inner ℝ v y = 0) hx' ?_ ?_ ?_
        · intro i v hvi
          exact horth i.castSucc (Fin.last m) (Fin.castSucc_ne_last i) v hvi y hy
        · simp
        · intro v w hv hw
          rw [inner_add_left, hv, hw]
          ring
      -- summability facts
      have hsumAB : Summable (fun z : (P' ⊔ B : Submodule ℤ E) => gm s (z : E)) := by
        exact summable_gm_Euclid s hs (P' ⊔ B)
      have hsumP' : Summable (fun x : P' => gm s (x : E)) := by
        exact summable_gm_Euclid s hs P'
      have hsumB : Summable (fun y : B => gm s (y : E)) := by
        dsimp [B]
        letI : DiscreteTopology (W (Fin.last m)) := hdisc (Fin.last m)
        exact summable_gm_Euclid s hs (W (Fin.last m))
      have htwopiece : (∑' z : (P' ⊔ B : Submodule ℤ E), gm s (z : E)) =
          (∑' x : P', gm s (x : E)) * (∑' y : B, gm s (y : E)) := by
        exact two_piece_sum (E := E) hs P' B horthPB hsumAB hsumP' hsumB
      -- induction hypothesis on the prefix
      have hih : (∑' z : P', gm s (z : E)) =
          ∏ i : Fin m, (∑' y : Wp i, gm s (y : E)) := by
        exact ih Wp P' rfl horthP' (fun i => by simpa [Wp] using hdisc i.castSucc) s hs
      -- assembly
      rw [hSsup]
      rw [htwopiece]
      rw [hih]
      rw [Fin.prod_univ_castSucc]

/-- Finite product rule for Gaussian masses over an internal direct sum of pairwise
elementwise-orthogonal lattices (paper identity rho_s(plus_i W_i) = prod_i rho_s(W_i),
used by the reduction in "A reverse Minkowski theorem").

Mathlib-only: E = EuclideanSpace ℝ (Fin n), pieces W : Fin k -> Submodule ℤ E pairwise
elementwise-orthogonal (horth: for i ≠ j every element of W i is orthogonal to every
element of W j, i.e. `inner ℝ x y = 0`), S = sup over i, W i is their internal sum
(given [DiscreteTopology S] and per-piece discreteness hdisc), s > 0.  Then
  sum' z : S, exp(-pi*‖(z:E)‖²/s²)  =  prod i : Fin k, (sum' y : W i, exp(-pi*‖(y:E)‖²/s²)).

PROOF ROUTE:
1. k = 0: S = ⊥ = {0}; LHS is exp(0) = 1; the empty product is 1.
2. Induct on k (peel the FIRST index 0 or the LAST index Fin.last (k-1)); for complete
   lattices split `⨆ i : Fin (k+1), f i = (⨆ i : Fin k, f i.castSucc) ⊔ f (Fin.last k)`
   (prove by antisymmetry with Fin.lastCases, or via the equiv Fin (k+1) ≃ Fin k ⊕ PUnit
   plus iSup_sum).
3. Prefix discreteness: each intermediate sup is ≤ S, so DiscreteTopology follows from the
   discrete topology of S - import `Commons.Lattice.Discrete.discreteTopology_of_le`
   (already committed in the commons).
4. Two-piece identity (prove inline): for submodules A B with every element of A orthogonal
   to every element of B (hence A ∩ B = {0}), addition (x,y) ↦ x+y is a bijection
   A × B ≃ A ⊔ B (surjective via Submodule.mem_sup; injective since x+y = x'+y' forces
   x−x' = y'−y ∈ A ∩ B = {0}), Pythagoras ‖x+y‖² = ‖x‖² + ‖y‖² (norm_add_sq), so with
   Equiv.tsum_eq (reindex) + Summable.tsum_prod (Fubini) + tsum_mul_left:
   sum over z : A ⊔ B of exp(-π‖z‖²/s²) = (sum over x : A)(sum over y : B) of the factors.
5. Orthogonality of the last piece with the prefix: via horth and Submodule.iSup_induction
   (inner product linearity).
6. Recurse with the induction hypothesis on Fin (k-1).
Notes: for z : P (P a submodule variable), (z : E) is its ambient value and z.2 its
membership.  Do NOT put `⨆ i, W i` in a TYPE position (Lean would attempt a type-level
sup); use the submodule variable S and the hypothesis hS instead.  `∏ i : Fin k, f i`
needs no extra hypotheses.  Summability over S comes from [DiscreteTopology S]; at each
per-piece sum use `letI : DiscreteTopology (W i) := hdisc i`. -/
theorem orthFam_mass_prod {n k : ℕ} (W : Fin k → Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (S : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hS : S = ⨆ i : Fin k, W i) [DiscreteTopology S]
    (horth : ∀ i j : Fin k, i ≠ j → ∀ x : EuclideanSpace ℝ (Fin n), x ∈ W i →
      ∀ y : EuclideanSpace ℝ (Fin n), y ∈ W j → inner ℝ x y = 0)
    (hdisc : ∀ i : Fin k, DiscreteTopology (W i))
    (s : ℝ) (hs : 0 < s) :
    (∑' z : S, Real.exp (-Real.pi * ‖(z : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) =
      ∏ i : Fin k, (∑' y : W i, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) := by
  classical
  change (∑' z : S, gm s (z : EuclideanSpace ℝ (Fin n))) =
    ∏ i : Fin k, (∑' y : W i, gm s (y : EuclideanSpace ℝ (Fin n)))
  exact massProdInd n k W S hS horth hdisc s hs

end Commons.Lattice.Gaussian