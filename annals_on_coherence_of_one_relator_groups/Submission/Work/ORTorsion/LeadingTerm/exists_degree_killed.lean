import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Grading.exists_top_degree
import Submission.Work.ORTorsion.Grading.commute_Tm
import Submission.Work.ORTorsion.Grading.Mk_Tm
import Submission.Work.ORTorsion.Grading.Mk_inclDN
import Submission.Work.ORTorsion.Grading.exists_single_smul_mem_range
import Submission.Work.ORTorsion.Grading.Mk_degPart
import Submission.Work.ORTorsion.Support.degPart_sum
import Submission.Work.ORTorsion.Support.mapSubAlg_degCoeff_mul

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped TensorProduct
open Work.ORTorsion
open Work.ORTorsion.LaurentBase

namespace Work.ORTorsion.LeadingTerm

/-! ## Auxiliary lemmas

The main theorem of this file is the leading-term descent `L5` of the torsion case: extracting the
degree-`(b₀+d)` component of `x • m`, where `b₀` is the top degree of `x` and `d` the top degree
of `m`, produces the degree-`b₀` coefficient of `x` together with a nonzero element of
`V ⊗[K] D(N)` that it kills.

Only three facts about the Laurent datum are used along the way:

* left `D(N)`-linearity of the coordinate maps `coord j : R → D(N)`;
* equivariance of `Mk j` under the diagonal action of `K[N]`;
* the diagonal action of `single (s^b) 1` on `V ⊗ D(N)` shifts the degree by exactly `b`.
-/

/-- **Left `D(N)`-linearity of the coordinate maps.**  For `a ∈ D(N)`, the degree-`j` coordinate
of the product `a · y` in `R ⊆ U` is `a` times the degree-`j` coordinate of `y`. -/
theorem coord_left_mul_DN {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (a : ↥(L.D Lb.N)) (j : ℤ) (y : ↥Lb.R) :
    Lb.coord j (⟨(a : U), Lb.DN_le_R a.2⟩ * y) = a * Lb.coord j y := by
  obtain ⟨S, hS⟩ := Lb.coord_expand y
  have hmul : (⟨(a : U), Lb.DN_le_R a.2⟩ : ↥Lb.R) * y
      = ∑ i ∈ S, Lb.rightMulU i (⟨((a * Lb.coord i y : ↥(L.D Lb.N)) : U),
          Lb.DN_le_R (a * Lb.coord i y).2⟩ : ↥Lb.R) := by
    conv_lhs => rw [← hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Lb.rightMulU_coe]
    rw [mul_assoc]
  have hsum : Lb.coord j (⟨(a : U), Lb.DN_le_R a.2⟩ * y)
      = ∑ i ∈ S, (if j = i then a * Lb.coord i y else 0) := by
    rw [hmul, map_sum]
    exact Finset.sum_congr rfl (fun i _ => Lb.coord_base j i (a * Lb.coord i y))
  rw [hsum, Finset.sum_ite_eq]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
  · rw [if_neg hj]
    have hz : Lb.coord j y = 0 := by
      have h1 : Lb.coord j y
          = ∑ i ∈ S, Lb.coord j (Lb.rightMulU i
              (⟨(Lb.coord i y : U), Lb.DN_le_R (Lb.coord i y).2⟩ : ↥Lb.R)) := by
        conv_lhs => rw [← hS, map_sum]
      calc Lb.coord j y
          = ∑ i ∈ S, Lb.coord j (Lb.rightMulU i
              (⟨(Lb.coord i y : U), Lb.DN_le_R (Lb.coord i y).2⟩ : ↥Lb.R)) := h1
        _ = ∑ i ∈ S, (if j = i then Lb.coord i y else 0) :=
              Finset.sum_congr rfl (fun i _ => Lb.coord_base j i (Lb.coord i y))
        _ = (if j ∈ S then Lb.coord j y else 0) :=
              Finset.sum_ite_eq S j (fun i => Lb.coord i y)
        _ = 0 := by rw [if_neg hj]
    rw [hz, mul_zero]

/-- The inclusion `V ⊗[K] D(N) → V ⊗[K] R` is injective: `Mk 0` is a left inverse. -/
theorem inclDN_injective {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ) :
    Function.Injective (inclDN Lb : V ⊗[K] ↥(L.D Lb.N) → V ⊗[K] ↥Lb.R) := by
  intro w w' h
  have h0 := congrArg (fun t => Mk Lb (V := V) 0 t) h
  simpa [Grading.mk_inclDN L Lb 0 w, Grading.mk_inclDN L Lb 0 w'] using h0

/-- The diagonal action of `single (s^b) 1` on `V ⊗[K] D(N)` sits in degree `b` alone. -/
theorem Mk_single_zpow_smul_inclDN_eq_zero {K : Type*} [Field K] {G : Type*} [Group G]
    {U : Type*} [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    {b j : ℤ} (hj : j ≠ b) (w : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb j ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) •
      (inclDN Lb w)) = 0 := by
  obtain ⟨w', hw'⟩ := Grading.exists_single_smul_mem_range L Lb (Lb.s ^ b) w
  have hdeg : deg φ (Lb.s ^ b) = b := deg_zpow (φ := φ) (s := Lb.s) Lb.hs_zpow b
  rw [hdeg] at hw'
  rw [hw', Grading.mk_tm L Lb j b, Grading.mk_inclDN L Lb (j - b) w']
  have hjb : j - b ≠ 0 := sub_ne_zero.mpr hj
  simp [hjb]

/-- The diagonal action of `single (s^b) 1` on `V ⊗[K] D(N)` is injective in its degree-`b`
component. -/
theorem Mk_single_zpow_smul_inclDN_ne_zero {K : Type*} [Field K] {G : Type*} [Group G]
    {U : Type*} [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (b : ℤ) {w : V ⊗[K] ↥(L.D Lb.N)} (hw : w ≠ 0) :
    Mk Lb b ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) •
      (inclDN Lb w)) ≠ 0 := by
  intro h0
  obtain ⟨w', hw'⟩ := Grading.exists_single_smul_mem_range L Lb (Lb.s ^ b) w
  have hdeg : deg φ (Lb.s ^ b) = b := deg_zpow (φ := φ) (s := Lb.s) Lb.hs_zpow b
  rw [hdeg] at hw'
  have hw'0 : w' = 0 := by
    have h1 : Mk Lb b ((MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) •
        (inclDN Lb w)) = w' := by
      rw [hw', Grading.mk_tm L Lb b b, sub_self, Grading.mk_inclDN L Lb 0 w', if_pos rfl]
    rw [h1] at h0
    exact h0
  have hX : (MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) •
      (inclDN Lb w) = 0 := by
    rw [hw', hw'0]
    simp
  have hmul_eq : (MonoidAlgebra.single (((Lb.s : H) ^ b)⁻¹) (1 : K) : MonoidAlgebra K H) *
      (MonoidAlgebra.single (Lb.s ^ b) (1 : K) : MonoidAlgebra K H) = 1 := by
    rw [MonoidAlgebra.single_mul_single, mul_one, inv_mul_cancel, MonoidAlgebra.one_def]
  have hincl : inclDN Lb w = 0 := by
    have hcongr := congrArg (fun t => (MonoidAlgebra.single (((Lb.s : H) ^ b)⁻¹) (1 : K) :
      MonoidAlgebra K H) • t) hX
    rw [smul_zero, ← mul_smul, hmul_eq, one_smul] at hcongr
    exact hcongr
  exact hw (inclDN_injective L Lb (by rw [hincl, map_zero]))

/-! ## The leading-term computation -/

/-- **The leading term.**  If `b₀` is the top degree of `x` (relative to a finite decomposition
`x = ∑_{b ∈ Sx} degPart φ b x` with `b ≤ b₀` for `b ∈ Sx`) and `d` is the top degree of `m`
(with `Mk i m = 0` above `d`), then the degree-`(b₀+d)` component of `x • m` is
`degCoeff Lb b₀ x` times the degree-`b₀` component of `single (s^b₀) 1 • inclDN (Mk d m)`. -/
theorem mk_top_eq {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
    (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    {x : MonoidAlgebra K H} {m : V ⊗[K] ↥Lb.R} {b₀ d : ℤ} {S Sx : Finset ℤ}
    (hSexp : m = ∑ i ∈ S, Tm Lb i (inclDN Lb (Mk Lb i m)))
    (hdS : d ∈ S)
    (hvan : ∀ i, d < i → Mk Lb i m = 0)
    (hx : x = ∑ b ∈ Sx, degPart φ b x)
    (hb₀ : b₀ ∈ Sx)
    (hle : ∀ b ∈ Sx, b ≤ b₀) :
    Mk Lb (b₀ + d) (x • m) =
      (degCoeff Lb b₀ x) •
        (Mk Lb b₀ ((MonoidAlgebra.single (Lb.s ^ b₀) (1 : K) : MonoidAlgebra K H) •
          (inclDN Lb (Mk Lb d m)))) := by
  conv_lhs => rw [hx, Finset.sum_smul, map_sum]
  have hterm : ∀ b ∈ Sx,
      Mk Lb (b₀ + d) ((degPart φ b x) • m) =
        if b = b₀ then (degCoeff Lb b₀ x) •
          (Mk Lb b₀ ((MonoidAlgebra.single (Lb.s ^ b₀) (1 : K) : MonoidAlgebra K H) •
            (inclDN Lb (Mk Lb d m)))) else 0 := by
    intro b hb
    by_cases hb_eq : b = b₀
    · rw [hb_eq]
      have hexp : Mk Lb (b₀ + d) ((degPart φ b₀ x) • m)
          = ∑ i ∈ S, Mk Lb (b₀ + d) ((degPart φ b₀ x) •
              (Tm Lb i (inclDN Lb (Mk Lb i m)))) := by
        conv_lhs => rw [hSexp, Finset.smul_sum, map_sum]
      have hsingle : ∀ i ∈ S, Mk Lb (b₀ + d) ((degPart φ b₀ x) •
            (Tm Lb i (inclDN Lb (Mk Lb i m))))
          = (degCoeff Lb b₀ x) • (if i = d then
              (Mk Lb b₀ ((MonoidAlgebra.single (Lb.s ^ b₀) (1 : K) : MonoidAlgebra K H) •
                (inclDN Lb (Mk Lb d m)))) else 0) := by
        intro i _
        rw [Grading.commute_Tm L Lb (degPart φ b₀ x) i (inclDN Lb (Mk Lb i m)),
          Grading.Mk_Tm L Lb (b₀ + d) i,
          Grading.Mk_degPart L Lb x b₀ (b₀ + d - i) (Mk Lb i m)]
        by_cases hid : i = d
        · rw [hid]
          simp
        · have hji : b₀ + d - i ≠ b₀ := by omega
          rw [if_neg hji, if_neg hid]
          simp
      rw [hexp, Finset.sum_congr rfl hsingle, ← Finset.smul_sum, Finset.sum_ite_eq',
        if_pos hdS, if_pos rfl]
    · have hb_lt : b < b₀ := lt_of_le_of_ne (hle b hb) hb_eq
      have hexp : Mk Lb (b₀ + d) ((degPart φ b x) • m)
          = ∑ i ∈ S, Mk Lb (b₀ + d) ((degPart φ b x) •
              (Tm Lb i (inclDN Lb (Mk Lb i m)))) := by
        conv_lhs => rw [hSexp, Finset.smul_sum, map_sum]
      rw [if_neg hb_eq, hexp]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Grading.commute_Tm L Lb (degPart φ b x) i (inclDN Lb (Mk Lb i m)),
        Grading.Mk_Tm L Lb (b₀ + d) i,
        Grading.Mk_degPart L Lb x b (b₀ + d - i) (Mk Lb i m)]
      by_cases hcond : b₀ + d - i = b
      · have hi : d < i := by omega
        rw [if_pos hcond, hvan i hi]
        simp
      · rw [if_neg hcond]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hb₀]

/-! ## The theorem -/

/-- **L5 (leading-term descent).**  If `0 ≠ x ∈ K[H]` and `0 ≠ m ∈ V ⊗[K] R` with `x • m = 0`,
then some nonzero degree component of `x` kills a nonzero element of `V ⊗[K] D(N)`. -/
theorem exists_degree_killed {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (x : MonoidAlgebra K H) (hx : x ≠ 0) (m : V ⊗[K] ↥Lb.R) (hm : m ≠ 0) (hxm : x • m = 0) :
    ∃ (b : ℤ) (z : V ⊗[K] ↥(L.D Lb.N)),
      LaurentBase.degCoeff Lb b x ≠ 0 ∧ z ≠ 0 ∧ (LaurentBase.degCoeff Lb b x) • z = 0 := by
  classical
  obtain ⟨d, S, hSexp, hd, htop⟩ := Grading.exists_top_degree L Lb m hm
  have hvan : ∀ i, d < i → Mk Lb i m = 0 := by
    intro i hi
    by_cases hiS : i ∈ S
    · exact htop i hiS hi
    · exact Grading.Mk_eq_zero_of_not_mem L Lb m S hSexp i hiS
  have hdS : d ∈ S := by
    by_contra hdS
    apply hd
    have h1 : Mk Lb d m = ∑ i ∈ S, Mk Lb d (Tm Lb i (inclDN Lb (Mk Lb i m))) := by
      conv_lhs => rw [hSexp]
      rw [map_sum]
    rw [h1]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Grading.mk_tm L Lb d i, Grading.mk_inclDN L Lb (d - i) (Mk Lb i m)]
    have hne : d - i ≠ 0 := by
      intro h0
      have hdi : d = i := by omega
      exact hdS (hdi ▸ hi)
    simp [hne]
  set Sx : Finset ℤ := x.coeff.support.image (deg φ) with hSxdef
  have hx' : x = ∑ b ∈ Sx, degPart φ b x := by
    rw [hSxdef]
    ext h
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [Support.coeff_degPart']
    by_cases hh : h ∈ x.coeff.support
    · have hS : deg φ h ∈ x.coeff.support.image (deg φ) :=
        Finset.mem_image.mpr ⟨h, hh, rfl⟩
      rw [Finset.sum_ite_eq' _ _ (fun _ => x.coeff h), if_pos hS]
    · rw [Finset.sum_ite_eq' _ _ (fun _ => x.coeff h), Finsupp.notMem_support_iff.mp hh]
      by_cases hS : deg φ h ∈ x.coeff.support.image (deg φ) <;> simp [hS]
  have hSxne : Sx.Nonempty := by
    rw [hSxdef]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine hx (by
      ext a
      have h0 : x.coeff a = 0 := Finsupp.notMem_support_iff.mp (fun ha => by
        have hmem : deg φ a ∈ x.coeff.support.image (deg φ) :=
          Finset.mem_image.mpr ⟨a, ha, rfl⟩
        rw [hne] at hmem
        exact Finset.notMem_empty _ hmem)
      simpa using h0)
  set b₀ := Sx.max' hSxne with hb₀def
  have hb₀mem : b₀ ∈ Sx := Finset.max'_mem _ _
  have hle : ∀ b ∈ Sx, b ≤ b₀ := fun b hb => Finset.le_max' _ _ hb
  have hb₀ne : degPart φ b₀ x ≠ 0 := by
    obtain ⟨h, hh, hhdeg⟩ := Finset.mem_image.mp (hSxdef ▸ hb₀mem)
    intro hcontra
    have hval : (degPart φ b₀ x).coeff h = x.coeff h := by
      rw [Support.coeff_degPart', if_pos hhdeg.symm]
    have hzero : x.coeff h = 0 := by
      have h0 : (0 : MonoidAlgebra K H).coeff h = x.coeff h := by
        rw [← hval, hcontra]
      simpa using h0.symm
    exact (Finsupp.mem_support_iff.mp hh) hzero
  have hc : LaurentBase.degCoeff Lb b₀ x ≠ 0 := by
    intro h0
    apply hb₀ne
    have h := Support.mapSubAlg_degCoeff_mul L Lb b₀ x
    rw [h0, map_zero, zero_mul] at h
    exact h.symm
  have hmain := mk_top_eq L Lb hSexp hdS hvan hx' hb₀mem hle
  refine ⟨b₀, Mk Lb b₀ ((MonoidAlgebra.single (Lb.s ^ b₀) (1 : K) : MonoidAlgebra K H) •
    (inclDN Lb (Mk Lb d m))), hc, ?_, ?_⟩
  · exact Mk_single_zpow_smul_inclDN_ne_zero L Lb b₀ hd
  · have h0 : Mk Lb (b₀ + d) (x • m) = 0 := by rw [hxm, map_zero]
    rw [hmain] at h0
    exact h0

end Work.ORTorsion.LeadingTerm
