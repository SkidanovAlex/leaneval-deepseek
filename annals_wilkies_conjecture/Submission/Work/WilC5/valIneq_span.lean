/-
  WilC5 — `valIneq_span`: the "span" step of the §4 layer.

  Wilkie's valuation inequality (`WilkiesDesign.CG.ValIneq`, the frozen `hVI`) says that at most
  `k` values of elements of `dcl(S ∪ {a₁,…,a_k})` can be `ℤ`-independent modulo the value group
  `Γ S` of the elementary substructure `S`.  This module extracts from it the statement needed in
  the Ressayre/vdDMM Lemma 4.2–4.4 bookkeeping: if `b ∈ dcl(S ∪ {y})` and `y` is *value-new* over
  `S` (the hypothesis `hynew`, `¬ IsUnitVal (c * y)` for `c ∈ S \ {0}`, i.e. `v(y) ∉ Γ S`), then
  the value of `b` is *not* independent from that of `y`: some nontrivial integer relation
  `c * b ^ q * y ^ n` is a unit, with `q ≠ 0`.

  Proof.  Apply `hVI` with `k = 1`, `a = (y)` and the two elements `b`, `y` (both in
  `dcl(S ∪ {y})`).  If their values were `ℤ`-independent modulo `Γ S` then `hVI` would give
  `2 ≤ 1`.  So there are `(q₀, q₁) ≠ 0` and `c ∈ S \ {0}` with `c * b ^ q₀ * y ^ q₁` a unit.  If
  `q₀ ≠ 0` this is the claim.  If `q₀ = 0` then `c * y ^ q₁` is a unit with `q₁ ≠ 0`; since an
  elementary substructure of a model of `TR` is real closed, `Γ S` is divisible, so this forces
  `c' ∈ S \ {0}` with `c' * y` a unit, contradicting `hynew`.

  The two auxiliary inputs are `Work.WilC5.model_pow_root` (in a model of `TR` every element has
  an `n`-th root of its square) and `Work.WilC5.elemSub_pow_root` (Tarski–Vaught: such a root lies
  in the elementary substructure).  The divisibility step is `unitVal_cancel_of_root` below.
-/
import Mathlib
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.model_pow_root
import Submission.Work.WilC5.elemSub_pow_root
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.dcl_elementary

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC5

/-- **The divisibility step of the value group `Γ S`.**

`S` is an elementary substructure of a *real closed* field: every `c ∈ S` has an `n`-th root of
its square in `S` (`elemSub_pow_root`, fed by the model hypothesis `hb`).  Consequently, if
`c ∈ S \ {0}`, `q ≠ 0` and `c * y ^ q` is a unit (i.e. `v(y) = -v(c)/q`), then `v(y)` already
lies in `Γ S`: some `c' ∈ S \ {0}` makes `c' * y` a unit.

The root is taken at the exponent `2n`: with `e ∈ S`, `e ^ (2n) = c ^ 2`, the element `e * y`
satisfies `(e * y) ^ (2n) = (c * y ^ n) ^ 2`, so `e * y` is a unit as soon as `c * y ^ n` is. -/
theorem unitVal_cancel_of_root {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M)
    (hb : ∀ (b : M) (m : ℕ), 1 ≤ m → ∃ z : M, z ^ m = b ^ 2)
    {y c : M} (hcS : c ∈ (S : Set M)) (hc : c ≠ 0) {q : ℤ} (hq : q ≠ 0)
    (h : WilkiesDesign.CG.IsUnitVal (c * y ^ q)) :
    ∃ c' ∈ (S : Set M), c' ≠ 0 ∧ WilkiesDesign.CG.IsUnitVal (c' * y) := by
  -- the case of a nonnegative exponent `n : ℕ`
  have hpos : ∀ (c : M), c ∈ (S : Set M) → c ≠ 0 → ∀ (n : ℕ), 1 ≤ n →
      WilkiesDesign.CG.IsUnitVal (c * y ^ n) →
      ∃ c' ∈ (S : Set M), c' ≠ 0 ∧ WilkiesDesign.CG.IsUnitVal (c' * y) := by
    intro c hcS hc0 n hn hcn
    obtain ⟨e, heS, he⟩ := elemSub_pow_root (M := M) S hb hcS (n := 2 * n) (by omega)
    refine ⟨e, heS, ?_, ?_⟩
    · intro he0
      rw [he0, zero_pow (by omega)] at he
      exact (pow_ne_zero 2 hc0) he.symm
    · have hy2 : (y ^ n) ^ 2 = y ^ (2 * n) := (pow_mul' y 2 n).symm
      have hpow : (e * y) ^ (2 * n) = (c * y ^ n) ^ 2 := by
        rw [mul_pow, he, mul_pow, hy2]
      have h2 : WilkiesDesign.CG.IsUnitVal ((e * y) ^ (2 * n)) := by
        rw [hpow]; exact Work.WilC5.IsUnitVal_pow hcn 2
      exact Work.WilC5.IsUnitVal_of_pow (by omega) h2
  rcases lt_trichotomy q 0 with hqlt | hqeq | hqgt
  · -- `q < 0`: invert, reducing to the nonnegative case at `c⁻¹`
    have hm : 1 ≤ (-q).toNat := by omega
    have hcD : c ∈ Work.WilC4.Dcl (S : Set M) ∅ := by
      rw [Work.WilC4.dcl_elementary S]; exact hcS
    have hcinvS : c⁻¹ ∈ (S : Set M) := by
      rw [← Work.WilC4.dcl_elementary S]; exact Work.WilC4.dcl_inv hcD hc
    have h' : WilkiesDesign.CG.IsUnitVal (c⁻¹ * y ^ ((-q).toNat)) := by
      have hinv : WilkiesDesign.CG.IsUnitVal ((c * y ^ q)⁻¹) := Work.WilC5.IsUnitVal_inv h
      have hstep1 : (c * y ^ q)⁻¹ = c⁻¹ * (y ^ q : M)⁻¹ := by rw [mul_inv_rev, mul_comm]
      have hstep2 : (y ^ q : M)⁻¹ = y ^ (-q) := (zpow_neg y q).symm
      have hstep3 : (y : M) ^ (-q) = y ^ ((-q).toNat) := by
        rw [← Int.toNat_of_nonneg (show (0 : ℤ) ≤ -q by omega)]
        exact zpow_natCast y ((-q).toNat)
      have heq : c⁻¹ * y ^ ((-q).toNat) = (c * y ^ q)⁻¹ := by rw [hstep1, hstep2, hstep3]
      rwa [← heq] at hinv
    exact hpos c⁻¹ hcinvS (inv_ne_zero hc) (-q).toNat hm h'
  · exact absurd hqeq hq
  · -- `q > 0`: read the integer power as a natural one
    have hnn : (0 : ℤ) ≤ q := le_of_lt hqgt
    have hm : 1 ≤ q.toNat := by omega
    have h' : WilkiesDesign.CG.IsUnitVal (c * y ^ q.toNat) := by
      have hy : (y ^ q.toNat : M) = y ^ q := by
        rw [← Int.toNat_of_nonneg hnn]
        exact (zpow_natCast y q.toNat).symm
      rw [hy]; exact h
    exact hpos c hcS hc q.toNat hm h'

theorem valIneq_span {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (hVI : WilkiesDesign.CG.ValIneq) (S : WilkiesDesign.CG.LRc.ElementarySubstructure M)
    {y b : M} (hy : y ≠ 0) (hb : b ≠ 0)
    (hbdef : ((S : Set M) ∪ {y}).Definable WilkiesDesign.CG.LRc {fun _ : Fin 1 => b})
    (hynew : ∀ c ∈ (S : Set M), c ≠ 0 → ¬ WilkiesDesign.CG.IsUnitVal (c * y)) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ n : ℤ, ∃ c ∈ (S : Set M), c ≠ 0 ∧
      WilkiesDesign.CG.IsUnitVal (c * b ^ q * y ^ n) := by
  -- in `M`, every element has an `n`-th root of its square
  have hbroot : ∀ (b : M) (n : ℕ), 1 ≤ n → ∃ z : M, z ^ n = b ^ 2 :=
    fun b n hn => model_pow_root (M := M) inferInstance b hn
  set a : Fin 1 → M := fun _ => y with ha'
  set bv : Fin 2 → M := ![b, y] with hbv
  have hb0 : ∀ j : Fin 2, bv j ≠ 0 := by
    intro j; fin_cases j <;> simp [hbv, hy, hb]
  -- `y` itself is definable from `S ∪ {y}`
  have hydef : ((S : Set M) ∪ {y}).Definable WilkiesDesign.CG.LRc {fun _ : Fin 1 => y} := by
    have h1 : ((S : Set M) ∪ {y}).Definable₁ WilkiesDesign.CG.LRc ({y} : Set M) :=
      Set.Definable.singleton_of_mem _ (Set.mem_union_right _ (Set.mem_singleton y))
    rw [Set.Definable₁] at h1
    have hs : ({v : Fin 1 → M | v 0 ∈ ({y} : Set M)}) = {fun _ : Fin 1 => y} := by
      ext v; simp [funext_iff]
    rwa [hs] at h1
  have hbdef' : ∀ j : Fin 2, ((S : Set M) ∪ Set.range a).Definable WilkiesDesign.CG.LRc
      {fun _ : Fin 1 => bv j} := by
    intro j
    have hr : Set.range a = ({y} : Set M) := by simp [ha']
    fin_cases j
    · simpa [hbv, hr] using hbdef
    · simpa [hbv, hr] using hydef
  -- `hVI` at `k = 1` (the generator `y`) and the two elements `b`, `y` forces a relation
  have hnotind : ¬ Work.WilC4.ValIndep (S : Set M) bv := by
    intro hind
    have h2 := hVI M S a bv hb0 hbdef' hind
    omega
  rw [Work.WilC4.ValIndep] at hnotind
  obtain ⟨q, hP⟩ := not_forall.mp hnotind
  obtain ⟨hPq, hqne⟩ := not_imp.mp hP
  obtain ⟨c, hcS, hc0, hunit⟩ := hPq
  simp only [Work.WilC4.zmono, Fin.prod_univ_two, hbv, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hunit
  rcases eq_or_ne (q 0) 0 with hz | hq0
  · -- `q 0 = 0`: the relation involves only `y`, which `hynew` and the divisibility of `Γ S` exclude
    have hq1 : q 1 ≠ 0 := by
      intro h1
      apply hqne
      funext j; fin_cases j <;> simp [hz, h1]
    have hunit' : WilkiesDesign.CG.IsUnitVal (c * y ^ (q 1)) := by
      simpa [hz] using hunit
    obtain ⟨c', hc'S, hc'0, hc'unit⟩ :=
      unitVal_cancel_of_root S hbroot hcS hc0 hq1 hunit'
    exact absurd hc'unit (hynew c' hc'S hc'0)
  · -- `q 0 ≠ 0`: the relation itself is the claim
    refine ⟨q 0, hq0, q 1, c, hcS, hc0, ?_⟩
    simpa [mul_assoc] using hunit

end Work.WilC5
