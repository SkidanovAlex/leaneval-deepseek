import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MMVec
import Submission.Work.HP.MMReindex
import Submission.Work.HP.DmixAux.Basic
import Submission.Work.HP.CoreDiag.sq_sub_two_sq

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP


private lemma isPrim_ne_zero_dl {ι : Type*} [Fintype ι] (v : ι → ℤ) (hv : IsPrim v) : v ≠ 0 := by
  intro h
  rw [IsPrim] at hv
  have h0 : (Finset.univ.gcd (0 : ι → ℤ)) = 0 := by
    rw [Finset.gcd_eq_zero_iff]; intro i _; rfl
  rw [← h] at h0
  rw [h0] at hv
  exact one_ne_zero hv.symm

/-- The Finset of ordered pairs `(x,y)` with `x, y ∈ Zy d n a B`, `x ≠ y` and `x ≠ -y`. -/
def QF (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ) :
    Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
  ((Zy_finite d n a B).toFinset ×ˢ (Zy_finite d n a B).toFinset).filter
    (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)

private lemma mem_Zy_iff (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ)
    (y : Fin (n + 1) → ℤ) (hy : y ∈ Xi d n B) :
    y ∈ Zy d n a B ↔ (((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a y ∧
      toR a ∈ Cgam (toR (veronese d n y)) (Real.log B)) := by
  simp only [Zy]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hy, h1, h2⟩

private lemma QF_subset_OmegaF (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ) :
    QF d n a B ⊆ (Omega_finite d n B).toFinset := by
  intro p hp
  rw [Set.Finite.mem_toFinset]
  rw [QF, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset] at hp
  exact ⟨hp.1.1.1, hp.1.2.1, hp.2.1, hp.2.2⟩

/-- The per-`a` identity: `N_V^loc(a,B)^2 - Δ_V^loc(a,B)` reindexed over pairs. -/
private lemma NVloc_sq_sub_DeltaLoc (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ)
    (B : ℝ) :
    NVloc d n a B ^ 2 - DeltaLoc d n a B =
      ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2 / 4) * (1 / eNorm a ^ 2) *
        ∑ p ∈ QF d n a B,
          (1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2)) := by
  have hNV : NVloc d n a B = (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
      ∑ x ∈ (Zy_finite d n a B).toFinset, 1 / eNorm (veronese d n x) := by
    rw [NVloc]
    change (1 / 2) * (Real.log B * ↑(bigW (wOf B)) / eNorm a) *
        (∑ᶠ x ∈ Zy d n a B, 1 / eNorm (veronese d n x)) = _
    rw [finsum_mem_eq_finite_toFinset_sum]
  have hDL : DeltaLoc d n a B =
      (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) ^ 2 *
      ∑ x ∈ (Zy_finite d n a B).toFinset, 1 / eNorm (veronese d n x) ^ 2 := by
    rw [DeltaLoc]
    change (1 / 2) * (Real.log B * ↑(bigW (wOf B)) / eNorm a) ^ 2 *
        (∑ᶠ x ∈ Zy d n a B, 1 / eNorm (veronese d n x) ^ 2) = _
    rw [finsum_mem_eq_finite_toFinset_sum]
  rw [hNV, hDL]
  have hQeq : (∑ x ∈ (Zy_finite d n a B).toFinset, 1 / eNorm (veronese d n x) ^ 2)
      = ∑ x ∈ (Zy_finite d n a B).toFinset, (1 / eNorm (veronese d n x)) ^ 2 := by
    apply Finset.sum_congr rfl; intro x _; rw [div_pow]; norm_num
  rw [hQeq]
  set Zf : Finset (Fin (n + 1) → ℤ) := (Zy_finite d n a B).toFinset with hZf
  set K : ℝ := Real.log B * ↑(bigW (wOf B)) / eNorm a with hK
  set S : ℝ := ∑ x ∈ Zf, 1 / eNorm (veronese d n x) with hS
  set Q : ℝ := ∑ x ∈ Zf, (1 / eNorm (veronese d n x)) ^ 2 with hQ
  have hneg : ∀ x ∈ Zf, -x ∈ Zf := by
    intro x hx
    rw [hZf, Set.Finite.mem_toFinset] at hx
    rw [hZf, Set.Finite.mem_toFinset]
    exact (DmixAux.Zy_neg_mem d n a B x).mp hx
  have hne : ∀ x ∈ Zf, x ≠ -x := by
    intro x hx h
    rw [hZf, Set.Finite.mem_toFinset] at hx
    have h0 : x = 0 := by
      funext i
      have hi := congrFun h i
      simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
      linarith
    exact isPrim_ne_zero_dl x hx.1.1 h0
  have hc : ∀ x, 1 / eNorm (veronese d n (-x)) = 1 / eNorm (veronese d n x) := by
    intro x; rw [eNorm_veronese_neg]
  have hD1a : S ^ 2 - 2 * Q = ∑ p ∈ (Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2),
      (1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2)) := by
    rw [hS, hQ, show Zf ×ˢ Zf = Zf.product Zf from
      (Finset.product_eq_sprod (s := Zf) (t := Zf)).symm]
    exact Work.HP.CoreDiag.sq_sub_two_sq Zf (fun y => 1 / eNorm (veronese d n y)) hneg hne hc
  have hD1 : S ^ 2 - 2 * Q = ∑ p ∈ QF d n a B,
      (1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2)) := by
    rw [hD1a, QF, hZf]
  rw [← hD1]
  simp only [hK]
  field_simp
  ring

/-- The dictionary: for `a` in the height ball and `p` in `Ω`, `p` contributes to `a` exactly
when `a ∈ Γ^{loc}_{p.1,p.2}(W) ∩ 𝒯^{loc}_{p.1,p.2}(A,α)`. -/
private lemma mem_QF_iff (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (A B : ℝ)
    (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) (hp : p ∈ Omega d n B)
    (ha : a ∈ primSet d n A (fun _ => True)) :
    p ∈ QF d n a B ↔ (a ∈ GamLoc d n p.1 p.2 (bigW (wOf B)) ∧
      a ∈ TlocSet d n p.1 p.2 A (Real.log B)) := by
  have h1 : p.1 ∈ Xi d n B := hp.1
  have h2 : p.2 ∈ Xi d n B := hp.2.1
  have hne1 : p.1 ≠ p.2 := hp.2.2.1
  have hne2 : p.1 ≠ -p.2 := hp.2.2.2
  have heA : eNorm a ≤ A := ha.2.1
  rw [QF, Finset.mem_filter, Finset.mem_product]
  rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  rw [mem_Zy_iff d n a B p.1 h1, mem_Zy_iff d n a B p.2 h2]
  simp only [GamLoc, TlocSet, Submodule.mem_inf, DmixAux.mem_latMod_eq_formEval,
    Set.mem_ofPred_eq]
  tauto

/-- The cofactor of the swap: the sum of `‖a‖^{-2}` over the primitive ball with `p ∈ QF a`
is exactly `𝓢*_2(Γ^{loc}_{p.1,p.2}(W); 𝒯^{loc}_{p.1,p.2}(A,α))`. -/
private lemma Sstar_eq_sum_ite (d n : ℕ) [DecidableEq (Mon d n)] (A B : ℝ)
    (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) (hp : p ∈ Omega d n B) :
    (∑ a ∈ (primSet_finite d n A (fun _ => True)).toFinset,
        (if p ∈ QF d n a B then 1 / eNorm a ^ 2 else 0))
      = Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B)))
          (TlocSet d n p.1 p.2 A (Real.log B)) := by
  have hfin : ({a : Mon d n → ℤ | a ∈ GamLoc d n p.1 p.2 (bigW (wOf B)) ∧ IsPrim a ∧
      a ∈ TlocSet d n p.1 p.2 A (Real.log B)}).Finite :=
    (primSet_finite d n A (fun _ => True)).subset fun a ha =>
      ⟨ha.2.1, ha.2.2.1, trivial⟩
  rw [Sstar]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hEq : hfin.toFinset = (primSet_finite d n A (fun _ => True)).toFinset.filter
      (fun a => p ∈ QF d n a B) := by
    ext a
    rw [Set.Finite.mem_toFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hg, hp', ht⟩
      refine ⟨⟨hp', ht.1, trivial⟩, ?_⟩
      rw [mem_QF_iff d n a A B p hp ⟨hp', ht.1, trivial⟩]
      exact ⟨hg, ht⟩
    · rintro ⟨⟨hp', heA, -⟩, hq⟩
      have hgh := (mem_QF_iff d n a A B p hp ⟨hp', heA, trivial⟩).mp hq
      exact ⟨hgh.1, hp', hgh.2⟩
  rw [hEq, ← Finset.sum_filter]

theorem DlocReindex (d n : ℕ) [DecidableEq (Mon d n)] (A B : ℝ) (hB : 1 < B) :
    Dloc d n A B = ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2 / 4) *
      ∑ᶠ p ∈ Omega d n B,
        Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B))) (TlocSet d n p.1 p.2 A (Real.log B)) /
          (eNorm (veronese d n p.1) * eNorm (veronese d n p.2)) := by
  classical
  rw [Dloc]
  rw [finsum_mem_eq_finite_toFinset_sum (fun a => NVloc d n a B ^ 2 - DeltaLoc d n a B)
        (primSet_finite d n A (fun _ => True))]
  set Pf : Finset (Mon d n → ℤ) := (primSet_finite d n A (fun _ => True)).toFinset with hPf
  have hA : ∑ a ∈ Pf, (NVloc d n a B ^ 2 - DeltaLoc d n a B)
      = ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2 / 4) *
        ∑ a ∈ Pf, (1 / eNorm a ^ 2) * ∑ p ∈ QF d n a B,
          (1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [NVloc_sq_sub_DeltaLoc]
    ring
  rw [hA]
  have hB' : ∑ a ∈ Pf, (1 / eNorm a ^ 2) * ∑ p ∈ QF d n a B,
        (1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))
      = ∑ᶠ p ∈ Omega d n B, Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B)))
          (TlocSet d n p.1 p.2 A (Real.log B)) /
          (eNorm (veronese d n p.1) * eNorm (veronese d n p.2)) := by
    have h1 : ∑ a ∈ Pf, (1 / eNorm a ^ 2) * ∑ p ∈ QF d n a B,
          (1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))
        = ∑ a ∈ Pf, ∑ p ∈ QF d n a B, (1 / eNorm a ^ 2) *
          ((1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]
    rw [h1]
    have h2a : ∀ a : Mon d n → ℤ, ∑ p ∈ QF d n a B, (1 / eNorm a ^ 2) *
          ((1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2)))
        = ∑ p ∈ (Omega_finite d n B).toFinset, (if p ∈ QF d n a B then (1 / eNorm a ^ 2) *
          ((1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))) else 0) := by
      intro a
      have hf : (Omega_finite d n B).toFinset.filter (fun p => p ∈ QF d n a B) = QF d n a B := by
        apply Finset.ext; intro p
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨QF_subset_OmegaF d n a B h, h⟩⟩
      rw [← Finset.sum_filter, hf]
    rw [Finset.sum_congr rfl (fun a _ => h2a a), Finset.sum_comm]
    have h3 : ∀ p ∈ (Omega_finite d n B).toFinset,
        ∑ a ∈ Pf, (if p ∈ QF d n a B then (1 / eNorm a ^ 2) *
          ((1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))) else 0)
        = ((1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))) *
          Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B)))
            (TlocSet d n p.1 p.2 A (Real.log B)) := by
      intro p hpO
      have hpOm : p ∈ Omega d n B := by rwa [Set.Finite.mem_toFinset] at hpO
      trans ∑ a ∈ Pf, ((1 / eNorm (veronese d n p.1)) * (1 / eNorm (veronese d n p.2))) *
            (if p ∈ QF d n a B then 1 / eNorm a ^ 2 else 0)
      · apply Finset.sum_congr rfl
        intro a _
        by_cases h : p ∈ QF d n a B
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      · rw [← Finset.mul_sum, hPf, Sstar_eq_sum_ite d n A B p hpOm]
    rw [Finset.sum_congr rfl h3]
    rw [finsum_mem_eq_finite_toFinset_sum (fun p => Sstar d n 2 (GamLoc d n p.1 p.2
          (bigW (wOf B))) (TlocSet d n p.1 p.2 A (Real.log B)) /
          (eNorm (veronese d n p.1) * eNorm (veronese d n p.2))) (Omega_finite d n B)]
    apply Finset.sum_congr rfl
    intro p _
    rw [one_div_mul_one_div, one_div, div_eq_mul_inv]
    ring
  rw [hB']

end Work.HP
