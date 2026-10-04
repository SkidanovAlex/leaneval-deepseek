import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.B3.compJetAuxB3
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open Filter
open scoped Topology

/-! ## Elementary helpers for the composition jet bound -/

private lemma quadForm_add {n : ℕ} (A B : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, (A i j + B i j) * ξ i * ξ j)
      = (∑ i, ∑ j, A i j * ξ i * ξ j) + (∑ i, ∑ j, B i j * ξ i * ξ j) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of a scalar multiple of a matrix. -/
private lemma quadForm_smul {n : ℕ} (c : ℝ) (A : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, (c * A i j) * ξ i * ξ j) = c * (∑ i, ∑ j, A i j * ξ i * ξ j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of the diagonal matrix `c • 1`. -/
private lemma quadForm_diag {n : ℕ} (c : ℝ) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, (if i = j then c else 0) * ξ i * ξ j) = c * ∑ i, (ξ i) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]; ring
  · intro j _ hj; rw [if_neg (Ne.symm hj)]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The norm of a `Pi.single` is at most the norm of its value (equality fails for the empty
index type, where `Pi.single` is the zero function). -/
private lemma norm_pi_single_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [SeminormedAddGroup α] (i : ι) (a : α) : ‖(Pi.single i a : ι → α)‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun j => by
    rcases eq_or_ne j i with h | h
    · subst h; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]; simpa using norm_nonneg a

/-- A product of numbers in `[0,1]` is at most `1`. -/
private lemma prod_le_one_of_le_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1a := h1 a (Finset.mem_insert_self a s)
      have h0s : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      have ih1 := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      calc f a * ∏ i ∈ s, f i ≤ 1 * 1 := mul_le_mul h1a ih1 h0s (by norm_num)
        _ = 1 := one_mul 1



/-- **The pointwise jet bound for the smooth composite `z ↦ Φ z (u z) (∂u z)`, uniform over `u`.**

This is the composition lever of `Work.Diff.STE.Lead.Gal.compJetBoundLoc` (same claim, same proof
route, recorded at this path so the B3 development can import it).  It is used twice: for the
coefficient family `(z,V) ↦ tmGKi z V p q` (which ignores the third argument) and for the residual
`Ψ`.

ROUTE (about 300 lines; do **not** attempt Faà di Bruno by hand).
Let `X := (Fin n → ℝ) × Mat × Mat3`, `g w := Φ w.1 w.2.1 w.2.2` and
`t := {w : X | ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0}` (open).
1. `Kc := {w : X | ‖w.1‖ ≤ (R + R')/2 ∧ (∀ i j, |w.2.1 i j| ≤ max KG 1) ∧ (∀ c i j, |w.2.2 c i j| ≤ max KG 1)}`
is compact; every state `(z, u z, ∂u z)` with `‖z‖ ≤ (R+R')/2` lies in it (use the `m = 0,1` cases of
the jet hypothesis) and, by ellipticity, satisfies `det (u z) ≠ 0`, so lies in `t`.  For `i ≤ k` the
map `w ↦ ‖iteratedFDerivWithin ℝ i g t w‖` is continuous on `t`
(`ContDiffOn.continuousOn_iteratedFDerivWithin`); take `C₀` for its maximum over `Kc ∩ t`.
2. Globalise: take a smooth bump `ψ` with `ψ = 1` on `‖z‖ ≤ R` and `tsupport ψ ⊆ {‖z‖ < R''}`,
`R < R'' < R'`, `0 ≤ ψ ≤ 1` (e.g. `Work.Diff.STE.B3.transport_exists_cutoff`).  Put
`ũ z := ψ z • u z + (1 - ψ z) • ((lam/2) • 1)` and
`F z := (ψ z • z, ũ z, fun c i j => pdR c (fun w => ũ w i j) z)`.  Then `F` is globally smooth
(on `tsupport ψ` use that `u` is smooth on `‖z‖ < R'` plus the "smooth on an open set times a bump
supported there" argument, cf. `contDiff_mul_of_tsupport_subset` in
`Submission/Work/Diff/STE/B3/transport_exists_A.lean`), `ũ ⪰ (lam/2) • 1` everywhere, `range F ⊆ t`
and `F z = (z, u z, ∂u z)` for `‖z‖ ≤ R`.
3. Apply the proved `Work.Diff.STE.flat.norm_iteratedFDeriv_comp_le_of_contDiffAt_ste`
(`Submission/Work/Diff/STE/flat/energy_apriori.lean`) to `g` and `F` at `x` with `‖x‖ ≤ R`:
`hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (F x)‖ ≤ C₀` and
`hD : ∀ i, 1 ≤ i → i ≤ k, ‖iteratedFDeriv ℝ i F x‖ ≤ D ^ i` for a fixed `D` built from `KG`
(`D := N * (KG + 1) ^ (k+1)`, `N := n + n^2 + n^3` is safe): bound the iterated derivative of `F` by
its mixed partials with `Work.Diff.STE.B3.norm_multilinear_le_of_basis`, the `u`-part of `F` being
`ψ • u` whose `pdVec`-jets up to order `k+1` are bounded by `KG` on `‖z‖ < R' ⊇ tsupport ψ`.
4. Convert back to `pdVec` with `Work.Diff.STE.Lead.Gal.pdVec_eq_iteratedFDeriv_on`
(`Submission/Work/Diff/STE/Lead/Gal/GardDefs.lean`, proved), using that `z ↦ Φ z (u z) (∂u z)`
agrees with `g ∘ F` on the open ball of radius `R'' > R`, so the jets at the points of `‖z‖ ≤ R`
coincide. -/
theorem compJetBoundB3 {n k : ℕ}
    (Φ : (Fin n → ℝ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → Fin n → ℝ) → ℂ)
    (R R' : ℝ) (hRR' : R < R')
    (hΦ : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) =>
        Φ w.1 w.2.1 w.2.2)
      {w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) |
        ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0})
    (lam KG : ℝ) (hlam : 0 < lam) (hKG : 0 ≤ KG) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : (Fin n → ℝ) → (Fin n → Fin n → ℝ)),
        (∀ i j : Fin n, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun z => u z i j)
          {z : Fin n → ℝ | ‖z‖ < R'}) →
        (∀ z : Fin n → ℝ, ‖z‖ < R' → ∀ ξ : Fin n → ℝ,
          lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, u z i j * ξ i * ξ j) →
        (∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → Fin n) (z : Fin n → ℝ) (i j : Fin n),
          ‖z‖ < R' →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((u y i j : ℝ) : ℂ)) z‖ ≤ KG) →
        ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ), ‖z‖ ≤ R →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ =>
            Φ y (u y) (fun c i j => Work.Diff.STE.pdR c (fun w : Fin n → ℝ => u w i j) y)) z‖
            ≤ C := by
  classical
  rcases lt_or_ge R 0 with hRneg | hR0
  · -- `R < 0` : the conclusion is vacuous
    refine ⟨0, le_rfl, ?_⟩
    intro u hu_sm hu_ell hu_jet m hm β z hz
    exact absurd hz (by have := norm_nonneg z; linarith)
  -- ### the smoothing parameters
  have hR'pos : 0 < R' := lt_of_le_of_lt hR0 hRR'
  set R2 : ℝ := (R + R') / 2 with hR2def
  set R3 : ℝ := (R2 + R') / 2 with hR3def
  have hRltR2 : R < R2 := by rw [hR2def]; linarith
  have hR2pos : 0 < R2 := by rw [hR2def]; linarith
  have hR2ltR3 : R2 < R3 := by rw [hR3def]; linarith
  have hR3ltR' : R3 < R' := by rw [hR3def]; linarith
  set ψ : ContDiffBump (0 : Fin n → ℝ) := ⟨R2, R3, hR2pos, hR2ltR3⟩ with hψdef
  have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑ψ) := ψ.contDiff
  have hψone : ∀ y : Fin n → ℝ, ‖y‖ ≤ R2 → ψ y = 1 := by
    intro y hy
    exact ψ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hy)
  have hψtsub : ∀ y : Fin n → ℝ, ψ y ≠ 0 → ‖y‖ ≤ R3 := by
    intro y hy
    have hy' : y ∈ tsupport (⇑ψ) := subset_tsupport (⇑ψ) hy
    rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy'
    exact hy'
  have hψnn : ∀ y, 0 ≤ ψ y := fun y => ψ.nonneg
  have hψle : ∀ y, ψ y ≤ 1 := fun y => ψ.le_one
  -- ### the open ball on which `u` is smooth, and the bump supported in it
  set B : Set (Fin n → ℝ) := {y | ‖y‖ < R'} with hBdef
  have hBopen : IsOpen B := by
    rw [hBdef]; exact isOpen_lt continuous_norm continuous_const
  have hψsupp : tsupport (⇑ψ) ⊆ B := by
    have hro : (ψ.rOut : ℝ) < R' := hR3ltR'
    rw [ContDiffBump.tsupport_eq]
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    rw [hBdef, Set.mem_ofPred_eq]
    linarith
  -- ### the constants
  set K0 : ℝ := max KG 1 with hK0def
  have hK01 : 1 ≤ K0 := by rw [hK0def]; exact le_max_right _ _
  have hK0nn : 0 ≤ K0 := le_trans zero_le_one hK01
  have hKGK0 : KG ≤ K0 := by rw [hK0def]; exact le_max_left _ _
  set Mbox : ℝ := K0 + lam / 2 + 1 with hMboxdef
  have hMboxK0 : K0 ≤ Mbox := by rw [hMboxdef]; linarith [hlam]
  have hMboxnn : 0 ≤ Mbox := le_trans hK0nn hMboxK0
  set Cu : ℝ := (n : ℝ) ^ 2 * ((max (n : ℝ) 1) ^ (k + 1) * K0) with hCudef
  set Cdu : ℝ := (n : ℝ) ^ 3 * ((max (n : ℝ) 1) ^ (k + 1) * K0) with hCdudef
  have hCunn : 0 ≤ Cu := by rw [hCudef]; positivity
  have hCdunn : 0 ≤ Cdu := by rw [hCdudef]; positivity
  set D : ℝ := 2 + Cu + Cdu with hDdef
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith
  have hDnn : 0 ≤ D := le_trans zero_le_one hD1
  -- ### the domain and the compact set of admissible states
  have hdetcont : Continuous (fun w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
      (Fin n → Fin n → Fin n → ℝ) => (Matrix.of w.2.1).det) :=
    Continuous.matrix_det (continuous_fst.comp continuous_snd)
  set t : Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ)) :=
    {w | ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0} with htdef
  have htopen : IsOpen t := by
    rw [htdef]
    have hset : {w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) |
          ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0}
        = {w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) |
            ‖w.1‖ < R'} ∩
          {w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) |
            (Matrix.of w.2.1).det ≠ 0} := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hset]
    exact IsOpen.inter (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)
      (isOpen_ne.preimage hdetcont)
  set Kball : Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ)) :=
    Metric.closedBall (0 : Fin n → ℝ) R3 ×ˢ
      (Metric.closedBall (0 : Fin n → Fin n → ℝ) Mbox ×ˢ
        Metric.closedBall (0 : Fin n → Fin n → Fin n → ℝ) Mbox) with hKballdef
  set Kell : Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ)) :=
    {w | ∀ ξ : Fin n → ℝ, (lam / 2) * ∑ i, (ξ i) ^ 2
      ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j} with hKelldef
  set Kbox : Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ)) :=
    Kball ∩ Kell with hKboxdef
  have hKballc : IsCompact Kball := by
    rw [hKballdef]
    exact (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hKellclosed : IsClosed Kell := by
    rw [hKelldef]
    have hset : {w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) |
          ∀ ξ : Fin n → ℝ, (lam / 2) * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j}
        = ⋂ ξ : Fin n → ℝ, {w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
            (Fin n → Fin n → Fin n → ℝ) |
            (lam / 2) * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j} := by
      ext w; simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    refine isClosed_iInter fun ξ => ?_
    have hcont : Continuous (fun w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → Fin n → ℝ) => ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j) := by
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      have hA : Continuous (fun w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
          (Fin n → Fin n → Fin n → ℝ) => w.2.1) := continuous_fst.comp continuous_snd
      have hAi : Continuous (fun A : Fin n → Fin n → ℝ => A i) :=
        continuous_apply (A := fun _ : Fin n => (Fin n → ℝ)) i
      have hAij : Continuous (fun A : Fin n → Fin n → ℝ => A i j) :=
        (continuous_apply (A := fun _ : Fin n => ℝ) j).comp hAi
      exact (((hAij.comp hA).mul continuous_const).mul continuous_const)
    exact isClosed_le continuous_const hcont
  have hKboxc : IsCompact Kbox := by
    rw [hKboxdef]
    exact hKballc.inter_right hKellclosed
  have hKbox_t : Kbox ⊆ t := by
    intro w hw
    rw [hKboxdef, Set.mem_inter_iff] at hw
    obtain ⟨hwb, hwe⟩ := hw
    rw [hKballdef, Set.mem_prod, Set.mem_prod] at hwb
    obtain ⟨h1, h2, h3⟩ := hwb
    rw [htdef, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
      linarith
    · rw [hKelldef, Set.mem_setOf_eq] at hwe
      refine Work.Diff.STE.flat.det_ne_zero_of_quadForm_le (Matrix.of w.2.1) (lam := lam / 2)
        (by linarith) ?_
      intro v
      simpa only [Matrix.of_apply] using hwe v
  -- ### the uniform bound for the jets of the nonlinearity on `Kbox`
  obtain ⟨C0, hC0nn, hC0bd⟩ :=
    Work.Diff.STE.flat.compact_iteratedFDeriv_bound
      (fun w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) =>
        Φ w.1 w.2.1 w.2.2) htopen hΦ hKboxc hKbox_t k
  refine ⟨(k.factorial : ℝ) * C0 * D ^ k, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0nn) (pow_nonneg hDnn _)
  intro u hu_sm hu_ell hu_jet m hm β z hz
  have hzball : ‖z‖ < R' := lt_of_le_of_lt hz hRR'
  have hzB : z ∈ B := by rw [hBdef, Set.mem_ofPred_eq]; exact hzball
  -- ### jet bounds for the real-valued entries of `u`
  have hpdRgen : ∀ (y : Fin n → ℝ), ‖y‖ < R' → ∀ (m' : ℕ), m' ≤ k + 1 →
      ∀ (γ : Fin m' → Fin n) (a b : Fin n),
      ‖Work.Diff.STE.pdRVec m' γ (fun w => u w a b) y‖ ≤ K0 := by
    intro y hy m' hm' γ a b
    have h1 := hu_jet m' hm' γ y a b hy
    rw [← Work.Diff.STE.B3.pdVecX_eq_pdVec, CJA.pdVecX_ofReal_eq γ (fun w => u w a b),
      Work.Diff.STE.B3.pdVecX_eq_pdRVec] at h1
    have h2 : ‖((Work.Diff.STE.pdRVec m' γ (fun w => u w a b) y : ℝ) : ℂ)‖
        = ‖Work.Diff.STE.pdRVec m' γ (fun w => u w a b) y‖ := Complex.ofRealLI.norm_map _
    rw [h2] at h1
    linarith
  have hpdR : ∀ (m' : ℕ), m' ≤ k + 1 → ∀ (γ : Fin m' → Fin n) (a b : Fin n),
      ‖Work.Diff.STE.pdRVec m' γ (fun w => u w a b) z‖ ≤ K0 :=
    fun m' hm' γ a b => hpdRgen z hzball m' hm' γ a b
  -- ### the globalised ellipticity matrix `ũ`
  set ref : Fin n → Fin n → ℝ := fun a b => if a = b then lam / 2 else 0 with hrefdef
  set ũ : (Fin n → ℝ) → (Fin n → Fin n → ℝ) :=
    fun y => ψ y • u y + (1 - ψ y) • ref with hũdef
  have hu_smP : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u B := by
    rw [hBdef]
    exact contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => hu_sm a b
  have hũu : ũ =ᶠ[nhds z] u := by
    have hb : Metric.ball (0 : Fin n → ℝ) R2 ∈ nhds z :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith)
    filter_upwards [hb] with y hy
    have hy' : ‖y‖ < R2 := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    have hψy : ψ y = 1 := hψone y (le_of_lt hy')
    rw [hũdef]
    simp [hψy]
  have hũ0 : ∀ y : Fin n → ℝ, ψ y = 0 → ũ y = ref := by
    intro y hψy
    rw [hũdef]
    simp [hψy]
  have hũell : ∀ y : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      (lam / 2) * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, ũ y i j * ξ i * ξ j := by
    intro y ξ
    by_cases hψy : ψ y = 0
    · rw [hũ0 y hψy, hrefdef, quadForm_diag]
    · have hynorm : ‖y‖ < R' := by
        have hy' : y ∈ tsupport (⇑ψ) := subset_tsupport (⇑ψ) hψy
        rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy'
        linarith
      have hell := hu_ell y hynorm ξ
      set S : ℝ := ∑ i, (ξ i) ^ 2 with hSdef
      set Q : ℝ := ∑ i, ∑ j, u y i j * ξ i * ξ j with hQdef
      have hSnn : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have hψynn : 0 ≤ ψ y := hψnn y
      have hψyle : ψ y ≤ 1 := hψle y
      have hexp : ∑ i, ∑ j, ũ y i j * ξ i * ξ j = ψ y * Q + (1 - ψ y) * ((lam / 2) * S) := by
        have h1 : ũ y = fun a b => ψ y * u y a b + (1 - ψ y) * ref a b := by
          rw [hũdef]; rfl
        conv_lhs => rw [h1]
        rw [quadForm_add, quadForm_smul, quadForm_smul,
          show (∑ i, ∑ j, ref i j * ξ i * ξ j) = (lam / 2) * S from by
            rw [hrefdef, quadForm_diag, hSdef]]
      rw [hexp]
      have hQS : ψ y * (lam * S) ≤ ψ y * Q := mul_le_mul_of_nonneg_left hell hψynn
      have hkey : (lam / 2) * S ≤ ψ y * (lam * S) + (1 - ψ y) * ((lam / 2) * S) := by
        nlinarith [hSnn, hψynn, hψyle, mul_nonneg hψynn hSnn, hlam]
      exact hkey.trans (add_le_add hQS le_rfl)
  -- ### the state maps
  set V : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) :=
    fun y => (y, u y, fun c a b => Work.Diff.STE.pdR c (fun w => u w a b) y) with hVdef
  set F : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) :=
    fun y => (ψ y • y, ũ y, fun c a b => Work.Diff.STE.pdR c (fun w => ũ w a b) y) with hFdef
  have hF1 : ∀ y : Fin n → ℝ, (F y).1 = ψ y • y := fun y => rfl
  have hF2 : ∀ y : Fin n → ℝ, (F y).2.1 = ũ y := fun y => rfl
  have hF3 : ∀ y : Fin n → ℝ, (F y).2.2
      = fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => ũ w a b) y := fun y => rfl
  have hFrng : Set.range F ⊆ t := by
    rintro w ⟨y, rfl⟩
    rw [htdef, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · have h1 : ‖(F y).1‖ ≤ R3 := by
        rw [hF1 y, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψnn y)]
        by_cases hψy : ψ y = 0
        · rw [hψy, zero_mul]; linarith
        · have hy' : ‖y‖ ≤ R3 := hψtsub y hψy
          calc ψ y * ‖y‖ ≤ 1 * R3 := mul_le_mul (hψle y) hy' (norm_nonneg y) zero_le_one
            _ = R3 := one_mul R3
      linarith
    · refine Work.Diff.STE.flat.det_ne_zero_of_quadForm_le (Matrix.of (ũ y)) (lam := lam / 2)
        (by linarith) ?_
      intro ξ
      simpa only [Matrix.of_apply] using hũell y ξ
  -- ### `F` is smooth
  have hψu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Fin n → ℝ => ψ y • u y) :=
    CJA.contDiff_smul_of_tsupport_subset hBopen hu_smP hψsm hψsupp
  have hũsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ũ := by
    rw [hũdef]
    exact hψu.add ((contDiff_const.sub hψsm).smul contDiff_const)
  have h3sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Fin n → ℝ => fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => ũ w a b) y) := by
    rw [contDiff_pi]
    intro c
    rw [contDiff_pi]
    intro a
    rw [contDiff_pi]
    intro b
    exact CJA.contDiff_pdR_top (contDiff_pi.mp (contDiff_pi.mp hũsm a) b) c
  have hFsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    rw [hFdef]
    exact (hψsm.smul contDiff_id).prodMk (hũsm.prodMk h3sm)
  have hgFsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Fin n → ℝ => Φ (F y).1 (F y).2.1 (F y).2.2) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact ((hΦ.contDiffAt (htopen.mem_nhds (hFrng ⟨y, rfl⟩))).comp y hFsm.contDiffAt)
  -- ### `F` and `V` agree near `z`
  have hFV : F =ᶠ[nhds z] V := by
    have hb : Metric.ball (0 : Fin n → ℝ) R2 ∈ nhds z :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith)
    filter_upwards [hb] with y hy
    have hy' : ‖y‖ < R2 := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    have hyb : Metric.ball (0 : Fin n → ℝ) R2 ∈ nhds y :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hy')
    have hψy : ψ y = 1 := hψone y (le_of_lt hy')
    have hũuy : ∀ a b : Fin n, (fun w : Fin n → ℝ => ũ w a b) =ᶠ[nhds y] (fun w => u w a b) := by
      intro a b
      filter_upwards [hyb] with w hw
      have hw' : ‖w‖ < R2 := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
      have hψw : ψ w = 1 := hψone w (le_of_lt hw')
      rw [hũdef]
      simp [hψw]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [hF1 y, hψy, one_smul]
    · rw [hF2 y]
      rw [hVdef]
      rw [hũdef]
      simp [hψy]
    · rw [hF3 y, hVdef]
      simp only
      funext c a b
      exact congrArg (fun (L : (Fin n → ℝ) →L[ℝ] ℝ) => L (Pi.single c 1))
        (Filter.EventuallyEq.fderiv_eq (hũuy a b))
  -- ### the jet bound for `V`
  have hVbound : ∀ (i : ℕ), 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i V z‖ ≤ D ^ i := by
    intro i hi1 hik
    have hId : ‖iteratedFDeriv ℝ i (fun y : Fin n → ℝ => y) z‖ ≤ 1 :=
      CJA.norm_iteratedFDeriv_id_le z hi1
    have hU : ‖iteratedFDeriv ℝ i u z‖ ≤ Cu := by
      rw [hCudef]
      refine CJA.norm_iteratedFDeriv_matrix_le_of_pdRVec_bound hBopen hu_smP hzB
        hK0nn (M := k + 1) (fun m' hm' γ a b => hpdR m' hm' γ a b) i (le_trans hik (by omega))
    have hDU : ‖iteratedFDeriv ℝ i
        (fun y : Fin n → ℝ => fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y) z‖
        ≤ Cdu := by
      rw [hCdudef]
      refine CJA.norm_iteratedFDeriv_mat3_le_of_pdRVec_bound hBopen hu_smP hzB
        hK0nn (M := k) (fun m' hm' γ a b => hpdR m' (by omega) γ a b) i hik
    have hTu : ContDiffAt ℝ (⊤ : ℕ∞) u z := hu_smP.contDiffAt (hBopen.mem_nhds hzB)
    have hTdu : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : Fin n → ℝ => fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y) z := by
      refine contDiffAt_pi.mpr fun c => contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u y a b) z :=
        (contDiffAt_pi.mp (contDiffAt_pi.mp hTu a)) b
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fderiv ℝ (fun y : Fin n → ℝ => u y a b)) z :=
        h1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h3 := h2.clm_apply (contDiffAt_const (c := ((Pi.single c (1 : ℝ)) : Fin n → ℝ)))
      simpa only [Work.Diff.STE.pdR] using h3
    have hpair : iteratedFDeriv ℝ i V z
        = (iteratedFDeriv ℝ i (fun y : Fin n → ℝ => y) z).prod
          ((iteratedFDeriv ℝ i u z).prod (iteratedFDeriv ℝ i
            (fun y : Fin n → ℝ => fun c a b : Fin n =>
              Work.Diff.STE.pdR c (fun w => u w a b) y) z)) := by
      show iteratedFDeriv ℝ i (fun y : Fin n → ℝ =>
          (y, u y, fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y)) z = _
      have h1 := iteratedFDeriv_prodMk (f := fun y : Fin n → ℝ => y)
        (g := fun y : Fin n → ℝ =>
          (u y, fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y))
        (x := z) (contDiffAt_id (x := z)) (hTu.prodMk hTdu) (i := i)
        (WithTop.coe_le_coe.mpr le_top)
      have h2 := iteratedFDeriv_prodMk (f := u)
        (g := fun y : Fin n → ℝ => fun c a b : Fin n =>
          Work.Diff.STE.pdR c (fun w => u w a b) y) (x := z) hTu hTdu (i := i)
        (WithTop.coe_le_coe.mpr le_top)
      exact h1.trans (congrArg
        (fun T => (iteratedFDeriv ℝ i (fun y : Fin n → ℝ => y) z).prod T) h2)
    calc ‖iteratedFDeriv ℝ i V z‖
        ≤ ‖iteratedFDeriv ℝ i (fun y : Fin n → ℝ => y) z‖
            + ‖(iteratedFDeriv ℝ i u z).prod (iteratedFDeriv ℝ i
              (fun y : Fin n → ℝ => fun c a b : Fin n =>
                Work.Diff.STE.pdR c (fun w => u w a b) y) z)‖ := by
          rw [hpair]; exact CJA.norm_prod_le _ _
      _ ≤ ‖iteratedFDeriv ℝ i (fun y : Fin n → ℝ => y) z‖
            + (‖iteratedFDeriv ℝ i u z‖ + ‖iteratedFDeriv ℝ i
              (fun y : Fin n → ℝ => fun c a b : Fin n =>
                Work.Diff.STE.pdR c (fun w => u w a b) y) z‖) :=
          add_le_add le_rfl (CJA.norm_prod_le _ _)
      _ ≤ 1 + (Cu + Cdu) := by linarith
      _ ≤ D := by rw [hDdef]; linarith
      _ ≤ D ^ i := by
          have h : D ^ 1 ≤ D ^ i := pow_le_pow_right₀ hD1 hi1
          simpa using h
  -- ### `F z` lies in the compact box
  have hFzK : F z ∈ Kbox := by
    have hψz : ψ z = 1 := hψone z (le_of_lt (lt_of_le_of_lt hz hRltR2))
    have hũz : ũ z = u z := hũu.eq_of_nhds
    have hduz : ∀ c a b : Fin n,
        Work.Diff.STE.pdR c (fun w => ũ w a b) z = Work.Diff.STE.pdR c (fun w => u w a b) z := by
      intro c a b
      have hev : (fun w : Fin n → ℝ => ũ w a b) =ᶠ[nhds z] (fun w => u w a b) := by
        filter_upwards [hũu] with w hw
        rw [hw]
      simp only [Work.Diff.STE.pdR]
      exact congrArg (fun (L : (Fin n → ℝ) →L[ℝ] ℝ) => L (Pi.single c 1))
        (Filter.EventuallyEq.fderiv_eq hev)
    have hz2 : ∀ a b : Fin n, |(F z).2.1 a b| ≤ Mbox := by
      intro a b
      have h2 : ‖Work.Diff.STE.pdRVec 0 (Fin.elim0 : Fin 0 → Fin n) (fun w => u w a b) z‖ ≤ K0 :=
        hpdR 0 (by omega) Fin.elim0 a b
      have h3 : Work.Diff.STE.pdRVec 0 (Fin.elim0 : Fin 0 → Fin n) (fun w => u w a b) z
          = u z a b := by
        simp only [Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList, List.ofFn_zero, List.foldr_nil]
      rw [h3, Real.norm_eq_abs] at h2
      rw [hF2 z, hũz]
      linarith [h2, hMboxK0]
    have hz3 : ∀ c a b : Fin n, |(F z).2.2 c a b| ≤ Mbox := by
      intro c a b
      have h3' : (F z).2.2 c a b = Work.Diff.STE.pdR c (fun w => u w a b) z := by
        have hF3' := hF3 z
        simp only [hF3']
        exact hduz c a b
      rw [h3']
      have h2 : ‖Work.Diff.STE.pdRVec 1 (fun _ : Fin 1 => c) (fun w => u w a b) z‖ ≤ K0 :=
        hpdR 1 (by omega) (fun _ : Fin 1 => c) a b
      have h3 : Work.Diff.STE.pdRVec 1 (fun _ : Fin 1 => c) (fun w => u w a b) z
          = Work.Diff.STE.pdR c (fun w => u w a b) z := by
        simp only [Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList, List.ofFn_succ,
          List.foldr_cons, List.ofFn_zero, List.foldr_nil]
      rw [h3, Real.norm_eq_abs] at h2
      linarith [h2, hMboxK0]
    rw [hKboxdef, Set.mem_inter_iff, hKballdef, Set.mem_prod, Set.mem_prod]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hF1 z, hψz, one_smul]
      calc ‖z‖ ≤ R := hz
        _ ≤ R3 := by linarith
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, pi_norm_le_iff_of_nonneg hMboxnn]
      intro a
      rw [pi_norm_le_iff_of_nonneg hMboxnn]
      intro b
      simpa only [Real.norm_eq_abs] using hz2 a b
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, pi_norm_le_iff_of_nonneg hMboxnn]
      intro c
      rw [pi_norm_le_iff_of_nonneg hMboxnn]
      intro a
      rw [pi_norm_le_iff_of_nonneg hMboxnn]
      intro b
      simpa only [Real.norm_eq_abs] using hz3 c a b
    · rw [hKelldef, Set.mem_setOf_eq]
      intro ξ
      rw [hF2 z]
      exact hũell z ξ
  have hFzt : F z ∈ t := hKbox_t hFzK
  -- ### the constant and the composition bound
  have hC0 : ∀ i ≤ m, ‖iteratedFDerivWithin ℝ i
      (fun w : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) =>
        Φ w.1 w.2.1 w.2.2) t (F z)‖ ≤ C0 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i htopen hFzt]
    exact hC0bd (F z) hFzK i (le_trans hi hm)
  have hDbound : ∀ (i : ℕ), 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i F z‖ ≤ D ^ i := by
    intro i hi1 him
    rw [(hFV.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hVbound i hi1 (le_trans him hm)
  have hcomp : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ (F y).1 (F y).2.1 (F y).2.2) z‖
      ≤ (m.factorial : ℝ) * C0 * D ^ m :=
    norm_iteratedFDeriv_comp_le' (t := t) hFrng htopen.uniqueDiffOn hΦ hFsm
      (WithTop.coe_le_coe.mpr le_top) z hC0 hDbound
  -- ### the conclusion
  have hgie : (fun y : Fin n → ℝ => Φ y (u y)
        (fun c i j => Work.Diff.STE.pdR c (fun w => u w i j) y))
      = fun y => Φ (V y).1 (V y).2.1 (V y).2.2 := by
    funext y
    rw [hVdef]
  have hev : (fun y : Fin n → ℝ => Φ (V y).1 (V y).2.1 (V y).2.2)
      =ᶠ[nhds z] (fun y => Φ (F y).1 (F y).2.1 (F y).2.2) := by
    filter_upwards [hFV] with y hy
    rw [hy]
  have hstep1 : Work.Diff.STE.pdVec m β
      (fun y : Fin n → ℝ => Φ y (u y) (fun c i j => Work.Diff.STE.pdR c (fun w => u w i j) y)) z
      = Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => Φ (F y).1 (F y).2.1 (F y).2.2) z := by
    rw [hgie, ← Work.Diff.STE.B3.pdVecX_eq_pdVec, ← Work.Diff.STE.B3.pdVecX_eq_pdVec]
    exact CJA.pdVecX_congr β hev
  have hfin : ‖Work.Diff.STE.pdVec m β
      (fun y : Fin n → ℝ => Φ y (u y) (fun c i j => Work.Diff.STE.pdR c (fun w => u w i j) y)) z‖
      ≤ (m.factorial : ℝ) * C0 * D ^ m := by
    rw [hstep1, Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m
      (fun y : Fin n → ℝ => Φ (F y).1 (F y).2.1 (F y).2.2) hgFsm z β]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hprod : (∏ j : Fin m,
        ‖(fun j : Fin m => (Pi.single (β j) (1 : ℝ) : Fin n → ℝ)) j‖) ≤ 1 :=
      prod_le_one_of_le_one _ _ (fun j _ => norm_nonneg _)
        (fun j _ => by simpa using norm_pi_single_le (β j) (1 : ℝ))
    calc ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ (F y).1 (F y).2.1 (F y).2.2) z‖
          * (∏ j : Fin m,
            ‖(fun j : Fin m => (Pi.single (β j) (1 : ℝ) : Fin n → ℝ)) j‖)
        ≤ ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ (F y).1 (F y).2.1 (F y).2.2) z‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ ≤ (m.factorial : ℝ) * C0 * D ^ m := by rw [mul_one]; exact hcomp
  calc ‖Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => Φ y (u y) (fun c i j => Work.Diff.STE.pdR c (fun w => u w i j) y)) z‖
      ≤ (m.factorial : ℝ) * C0 * D ^ m := hfin
    _ ≤ (k.factorial : ℝ) * C0 * D ^ k := by
        have h1 : (m.factorial : ℝ) ≤ (k.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le hm
        have h2 : D ^ m ≤ D ^ k := pow_le_pow_right₀ hD1 hm
        calc (m.factorial : ℝ) * C0 * D ^ m
            ≤ (k.factorial : ℝ) * C0 * D ^ m :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hC0nn) (pow_nonneg hDnn _)
          _ ≤ (k.factorial : ℝ) * C0 * D ^ k :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg _) hC0nn)

end Work.Diff.STE.B3
