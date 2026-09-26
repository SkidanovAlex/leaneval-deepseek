import Mathlib
import Submission.Work.FreeProduct.IdealImDirect
import Submission.Work.FreeProduct.IdealIpDirect
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.Tools
import Submission.Work.FreeProduct.orbit_corollary
import Submission.Work.FreeProduct.T_zpow_injective
import Submission.Work.FreeProduct.Canonical
import Submission.Work.FreeProduct.Decomp
import Submission.Work.FreeProduct.LengthFacts
import Submission.Work.FreeProduct.ClaimL3

/-!
# The right ideal `(T - 1)² ℂ[Γ] + S (T - 1)² ℂ[Γ]` is a direct sum

CKMRV, Proposition 3.1 for `ℐ = (T-I)²R + S(T-I)²R`, stated in the group algebra
`RR = ℂ[ℤ/2 ∗ ℤ/3]` of the free product `Γ = ℤ/2 ∗ ℤ/3`, with `X = x = S`,
`Y = y = ST` and `TT = X * Y = T`:

  `(T-1)² * a + X * (T-1)² * b = 0  →  a = 0 ∧ b = 0`.

This is the directness of the sum, i.e. freeness of the right `RR`-module `ℐ` of rank two.

Following the paper, the proof multiplies the relation by `X` and splits it with the
idempotents `(1 ± X)/2`:

* `(1 + X) · (T-1)² (a+b) = 0` exhibits `(T-1)²(a+b)` as an element of the `(-1)`-eigenspace
  `(X-1)·RR` of left multiplication by `X`.  This is killed by `IdealImDirect`
  (the `ℐ_-` half of the paper's argument, proved in
  `Submission/Work/FreeProduct/IdealImDirect.lean`): `(T-1)²u ∈ (X-1)·RR → u = 0`.
* `(1 - X) · (T-1)² (a-b) = 0` exhibits `(T-1)²(a-b)` as an element of `(X+1)·RR`, and
  `(1-X)(T-1) = -(1-X)(1+Y)` turns this into `(1-X)(1+Y)(T-1)(a-b) = 0`, which is killed by
  `Ip_torsion` (the `ℐ_+` half, proved below).

The `ℐ_+` half is the paper's "case of `ℐ_+`": from `(T-1)u = (y²-y+1)(x+1) r` one gets
`(T-1)u = (y²x + y² - yx - y + x + 1) r`; after replacing `r` by an `NX`-supported
representative (no reduced word starts with `x`), a maximal-length `γ` in its support is
chosen and the coefficient of `(T-1)u` at `y x γ` is computed: only the summand `- yx · r`
contributes, giving `- coeff r γ ≠ 0`, while every other `⟨T⟩`-translate of `y x γ` is longer
than the whole support of `(T-1)u`.  The discrete-integral corollary
`Work.FreeProduct.orbit_corollary` (CKMRV Corollary 3.4) gives a contradiction.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

namespace IpDirect

theorem ker_one_add_X {v : RR} (h : (1 + X) * v = 0) : ∃ w, v = (X - 1) * w := by
  have hX : X * v = -v := by
    have h' := h
    rw [add_mul, one_mul] at h'
    exact eq_neg_of_add_eq_zero_right h'
  refine ⟨(-(2⁻¹ : ℂ)) • v, ?_⟩
  have h2 : (X - 1) * v = -(v + v) := by
    rw [show (X - 1) * v = X * v - v from by rw [sub_mul, one_mul], hX]
    abel
  rw [mul_smul_comm, h2, smul_neg, neg_smul, neg_neg, ← two_smul ℂ v, smul_smul,
    show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

theorem ker_one_sub_X {v : RR} (h : (1 - X) * v = 0) : ∃ w, v = (X + 1) * w := by
  have hX : X * v = v := by
    have h' : v - X * v = 0 := by simpa [sub_mul, one_mul] using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨(2⁻¹ : ℂ) • v, ?_⟩
  have h2 : (X + 1) * v = v + v := by
    rw [show (X + 1) * v = X * v + v from by rw [add_mul, one_mul], hX]
  rw [mul_smul_comm, h2, ← two_smul ℂ v, smul_smul,
    show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

theorem exists_NX_of_add_one (γ : FP) :
    ∃ u : RR, (X + 1) * u = (X + 1) * MonoidAlgebra.of ℂ FP γ ∧
      ∀ δ ∈ (MonoidAlgebra.coeff u).support, NX δ := by
  by_cases h : NX γ
  · exact ⟨MonoidAlgebra.of ℂ FP γ, rfl, by
      intro δ hδ
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single] at hδ
      have h1 : δ = γ := by simpa using Finsupp.support_single_subset hδ
      rw [h1]; exact h⟩
  · have hst : (Monoid.CoprodI.Word.equiv γ).fstIdx = some false := by
      rw [NX] at h; exact not_not.mp h
    obtain ⟨γ', hγ', hNX'⟩ := exists_X_dcomp γ hst
    refine ⟨MonoidAlgebra.of ℂ FP γ', ?_, ?_⟩
    · have hX : (X + 1) * X = X + 1 := by rw [add_mul, one_mul, X_mul_X]; abel
      have h1 : MonoidAlgebra.of ℂ FP γ = X * MonoidAlgebra.of ℂ FP γ' := by
        rw [hγ', map_mul]; rfl
      calc (X + 1) * MonoidAlgebra.of ℂ FP γ' = ((X + 1) * X) * MonoidAlgebra.of ℂ FP γ' := by
            rw [hX]
        _ = (X + 1) * (X * MonoidAlgebra.of ℂ FP γ') := by rw [mul_assoc]
        _ = (X + 1) * MonoidAlgebra.of ℂ FP γ := by rw [← h1]
    · intro δ hδ
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single] at hδ
      have h1 : δ = γ' := by simpa using Finsupp.support_single_subset hδ
      rw [h1]; exact hNX'

theorem NX_canon_add_one (r : RR) :
    ∃ r' : RR, (X + 1) * r' = (X + 1) * r ∧
      ∀ γ ∈ (MonoidAlgebra.coeff r').support, NX γ := by
  classical
  refine MonoidAlgebra.induction_on (R := ℂ) (M := FP)
    (motive := fun y => ∃ y' : RR, (X + 1) * y' = (X + 1) * y ∧
      ∀ γ ∈ (MonoidAlgebra.coeff y').support, NX γ) r ?_ ?_ ?_
  · intro m
    exact exists_NX_of_add_one m
  · intro a b ha hb
    obtain ⟨a', ha', haX⟩ := ha
    obtain ⟨b', hb', hbX⟩ := hb
    refine ⟨a' + b', ?_, ?_⟩
    · rw [mul_add, ha', hb', mul_add]
    · intro γ hγ
      have h : MonoidAlgebra.coeff (a' + b') γ =
          MonoidAlgebra.coeff a' γ + MonoidAlgebra.coeff b' γ := by
        rw [MonoidAlgebra.coeff_add]; rfl
      rw [Finsupp.mem_support_iff] at hγ
      rw [h] at hγ
      by_cases h0 : MonoidAlgebra.coeff a' γ = 0
      · refine hbX γ ?_
        rw [Finsupp.mem_support_iff]
        intro hb0
        exact hγ (by rw [h0, hb0, add_zero])
      · exact haX γ (Finsupp.mem_support_iff.mpr h0)
  · intro c a ha
    obtain ⟨a', ha', haX⟩ := ha
    refine ⟨c • a', ?_, ?_⟩
    · rw [mul_smul_comm, mul_smul_comm, ha']
    · intro γ hγ
      refine haX γ (Finsupp.mem_support_iff.mpr ?_)
      intro h0
      rw [Finsupp.mem_support_iff] at hγ
      refine hγ ?_
      simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, h0, smul_zero]

theorem MUp_mul_X_add_one_expand :
    MUp * (X + 1) = MonoidAlgebra.of ℂ FP (y2*x) + MonoidAlgebra.of ℂ FP y2
      - MonoidAlgebra.of ℂ FP (y*x) - MonoidAlgebra.of ℂ FP y + MonoidAlgebra.of ℂ FP x + 1 := by
  have h1 : MonoidAlgebra.of ℂ FP (y2*x) =
      MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x := map_mul _ _ _
  have h2 : MonoidAlgebra.of ℂ FP (y*x) =
      MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x := map_mul _ _ _
  rw [h1, h2, MUp, X, Y, Y2]
  noncomm_ring

theorem expand_mul (r : RR) :
    MUp * (X + 1) * r =
      MonoidAlgebra.of ℂ FP (y2*x) * r + MonoidAlgebra.of ℂ FP y2 * r
        - MonoidAlgebra.of ℂ FP (y*x) * r - MonoidAlgebra.of ℂ FP y * r
        + MonoidAlgebra.of ℂ FP x * r + r := by
  rw [MUp_mul_X_add_one_expand]
  noncomm_ring

theorem inv_y2_mul_yx (γ : FP) : y2⁻¹ * (y * x * γ) = y2 * x * γ := by
  rw [ImDirect.y2_inv]
  calc y * (y * x * γ) = y * (y * (x * γ)) := by rw [mul_assoc]
    _ = (y * y) * (x * γ) := (mul_assoc y y (x * γ)).symm
    _ = y2 * (x * γ) := by rw [y_mul_y]
    _ = y2 * x * γ := (mul_assoc y2 x γ).symm

theorem inv_y_mul_yx (γ : FP) : y⁻¹ * (y * x * γ) = x * γ := by
  rw [y_inv]
  calc y2 * (y * x * γ) = y2 * (y * (x * γ)) := by rw [mul_assoc]
    _ = (y2 * y) * (x * γ) := (mul_assoc y2 y (x * γ)).symm
    _ = x * γ := by rw [y2_mul_y, one_mul]

theorem coeff_MUp_mul_X_add_one (r : RR) {γ : FP} (hγ : MonoidAlgebra.coeff r γ ≠ 0)
    (hmax : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ elen γ)
    (hNX : ∀ δ ∈ (MonoidAlgebra.coeff r).support, NX δ) :
    MonoidAlgebra.coeff (MUp * (X + 1) * r) (y * x * γ) = - MonoidAlgebra.coeff r γ := by
  have hrlen : ImDirect.rlen r ≤ elen γ := by
    rw [ImDirect.rlen]
    exact Finset.sup_le hmax
  have hNXγ : NX γ := hNX γ (Finsupp.mem_support_iff.mpr hγ)
  have h0 : MonoidAlgebra.coeff r (x * y2 * x * γ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by rw [elen_xy2x_mul hNXγ]; omega)
  have h1 : MonoidAlgebra.coeff r (y2 * x * γ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by rw [elen_y2x_mul hNXγ]; omega)
  have h2 : MonoidAlgebra.coeff r (x * γ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by rw [elen_x_mul hNXγ]; omega)
  have h3 : MonoidAlgebra.coeff r (x * y * x * γ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by rw [elen_xyx_mul hNXγ]; omega)
  have h4 : MonoidAlgebra.coeff r (y * x * γ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by rw [elen_yx_mul hNXγ]; omega)
  rw [expand_mul]
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, Finsupp.add_apply,
    Finsupp.sub_apply, ImDirect.coeff_of_mul']
  rw [ImDirect.inv_y2x_mul_yx, inv_y2_mul_yx, ImDirect.inv_yx_mul_yx, inv_y_mul_yx,
    ImDirect.inv_x_mul_yx]
  rw [h0, h1, h3, h2, h4]
  ring

theorem coeff_MUp_mul_X_add_one_eq_zero (r : RR) {δ : FP}
    (hδ : ImDirect.rlen r + 2 < elen δ) :
    MonoidAlgebra.coeff (MUp * (X + 1) * r) δ = 0 := by
  have h0 : MonoidAlgebra.coeff r ((y2*x)⁻¹ * δ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by
      have h := ImDirect.elen_smul_ge (y2*x) δ
      have h2 := ImDirect.elen_y2x_le
      omega)
  have h1 : MonoidAlgebra.coeff r (y2⁻¹ * δ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by
      have h := ImDirect.elen_smul_ge y2 δ
      have h2 := ImDirect.elen_y2_le
      omega)
  have h2 : MonoidAlgebra.coeff r ((y*x)⁻¹ * δ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by
      have h := ImDirect.elen_smul_ge (y*x) δ
      have h2 := ImDirect.elen_yx_le
      omega)
  have h3 : MonoidAlgebra.coeff r (y⁻¹ * δ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by
      have h := ImDirect.elen_smul_ge y δ
      have h2 := ImDirect.elen_y_le
      omega)
  have h4 : MonoidAlgebra.coeff r (x⁻¹ * δ) = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by
      have h := ImDirect.elen_smul_ge x δ
      have h2 := ImDirect.elen_x_le
      omega)
  have h5 : MonoidAlgebra.coeff r δ = 0 :=
    ImDirect.coeff_eq_zero_of_rlen_lt (by omega)
  rw [expand_mul]
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, Finsupp.add_apply,
    Finsupp.sub_apply, ImDirect.coeff_of_mul']
  rw [h0, h1, h2, h3, h4, h5]
  ring

end IpDirect

/-! ## Part 3: the `ℐ_+` core and the two halves -/

/-- **The `ℐ_+` core.**  If `(T-1)u = (y²-y+1)(x+1) r` then `(T-1)u = 0`: the `⟨T⟩`-orbit
of the witness `y x γ` meets the support of `(T-1)u` only once, contradicting the
discrete-integral corollary `orbit_corollary`. -/
theorem TT_sub_one_mul_eq_zero_of_MUp_Xp1 (u r : RR)
    (h : (TT - 1) * u = MUp * (X + 1) * r) : (TT - 1) * u = 0 := by
  obtain ⟨r', hr', hNX⟩ := IpDirect.NX_canon_add_one r
  have hrr : MUp * (X + 1) * r = MUp * (X + 1) * r' := by
    simp only [mul_assoc]
    rw [hr']
  have h2 : (TT - 1) * u = MUp * (X + 1) * r' := by rw [h, hrr]
  by_contra hvne
  have hr'ne : r' ≠ 0 := by
    intro h0
    exact hvne (by rw [h2, h0, mul_zero])
  obtain ⟨γ, hγc, hγlen⟩ := ImDirect.exists_max_elen hr'ne
  have hNXγ : NX γ := hNX γ (Finsupp.mem_support_iff.mpr hγc)
  have hmax : ∀ δ ∈ (MonoidAlgebra.coeff r').support, elen δ ≤ elen γ := by
    intro δ hδ
    rw [hγlen]
    exact ImDirect.coeff_ne_zero_elen_le (Finsupp.mem_support_iff.mp hδ)
  exact orbit_corollary T_zpow_injective (w := (TT - 1) * u) (u := u) (γ := y * x * γ)
    (c := -(MonoidAlgebra.coeff r' γ)) rfl
    (by rw [h2, IpDirect.coeff_MUp_mul_X_add_one r' hγc hmax hNX])
    (neg_ne_zero.mpr hγc)
    (by
      intro n hn
      rw [h2]
      refine IpDirect.coeff_MUp_mul_X_add_one_eq_zero r' ?_
      have h3 := ImDirect.elen_T_zpow_mul_yx hNXγ hn
      rw [hγlen] at h3
      omega)

/-- `(y² - y + 1)(y+1) = 2`. -/
theorem MUp_mul_Y_add_one : MUp * (Y + 1) = 2 := by
  have h : MUp * (Y + 1) = ((Y2 * Y + Y2) - (Y * Y + Y)) + (Y + 1) := by
    rw [MUp, add_mul, sub_mul, mul_add, mul_add, one_mul, mul_one, mul_one]
  rw [h, Y2_mul_Y, Y_mul_Y]
  rw [show (2 : RR) = 1 + 1 by norm_num]
  abel

/-- **The `ℐ_+` half of Proposition 3.1** in "torsion" form: `(1 - X)(1 + Y)(T-1)u = 0`
forces `u = 0`. -/
theorem Ip_torsion {u : RR} (h : (1 - X) * (1 + Y) * (TT - 1) * u = 0) : u = 0 := by
  set v : RR := (TT - 1) * u with hv
  have h1 : (1 - X) * ((1 + Y) * v) = 0 := by
    have h' : (1 - X) * (1 + Y) * v = 0 := by rw [hv, ← mul_assoc]; exact h
    rwa [mul_assoc] at h'
  obtain ⟨w, hw⟩ := IpDirect.ker_one_sub_X h1
  have h2 : (2 : ℂ) • v = MUp * (X + 1) * w := by
    have hh : MUp * ((1 + Y) * v) = MUp * ((X + 1) * w) := by rw [hw]
    have e1 : MUp * ((1 + Y) * v) = (2 : ℂ) • v := by
      rw [add_comm (1 : RR) Y, ← mul_assoc, MUp_mul_Y_add_one, Algebra.smul_def, map_ofNat]
    rw [e1] at hh
    rwa [← mul_assoc] at hh
  have h3 : v = MUp * (X + 1) * ((2⁻¹ : ℂ) • w) := by
    have h := congrArg (fun z : RR => (2⁻¹ : ℂ) • z) h2
    rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] at h
    rw [h, ← mul_smul_comm]
  have h4 : (TT - 1) * u = MUp * (X + 1) * ((2⁻¹ : ℂ) • w) := by rw [← hv]; exact h3
  exact ImDirect.TT_sub_one_injective u (TT_sub_one_mul_eq_zero_of_MUp_Xp1 u _ h4)

/-- `(1 - X)(T-1) = -(1 - X)(1 + Y)`. -/
theorem one_sub_X_mul_TT_sub_one : (1 - X) * (TT - 1) = -((1 - X) * (1 + Y)) := by
  have lhs : (1 - X) * (TT - 1) = X * Y - 1 - (Y - X) := by
    rw [← X_mul_Y, sub_mul, one_mul, mul_sub, mul_one, ← mul_assoc, X_mul_X, one_mul]
  have rhs : -((1 - X) * (1 + Y)) = X * Y - 1 - (Y - X) := by
    rw [sub_mul, one_mul, mul_add, mul_one]
    abel
  rw [lhs, rhs]

/-! ## Part 4: the assembly -/

/-- **CKMRV, Proposition 3.1 for `ℐ`.**  The sum `(T-1)²·RR + X(T-1)²·RR` is direct, i.e. the
only solution of `(T-1)² a + X (T-1)² b = 0` is `a = b = 0`. -/
theorem idealI_direct {a b : Work.FreeProduct.RR}
    (h : (Work.FreeProduct.TT - 1) ^ 2 * a + Work.FreeProduct.X * (Work.FreeProduct.TT - 1) ^ 2 * b = 0) :
    a = 0 ∧ b = 0 := by
  set A : RR := (TT - 1) ^ 2 with hA
  have h1 : A * a = -(X * A * b) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [hA] using h
  have h2 : X * A * a = -(A * b) := by
    calc X * A * a = X * (A * a) := by rw [mul_assoc]
      _ = X * (-(X * A * b)) := by rw [h1]
      _ = -(X * (X * A * b)) := by rw [mul_neg]
      _ = -((X * X) * A * b) := by rw [← mul_assoc, ← mul_assoc]
      _ = -(A * b) := by rw [X_mul_X, one_mul]
  have hsum : (1 + X) * (A * (a + b)) = 0 := by
    have e : (1 + X) * (A * (a + b)) = (A * a + X * A * a) + (A * b + X * A * b) := by
      noncomm_ring
    rw [e, h1, h2]; abel
  have hdiff : (1 - X) * (A * (a - b)) = 0 := by
    have e : (1 - X) * (A * (a - b)) = (A * a - X * A * a) - (A * b - X * A * b) := by
      noncomm_ring
    rw [e, h1, h2]; abel
  have hab : a + b = 0 := by
    obtain ⟨w, hw⟩ := IpDirect.ker_one_add_X (v := A * (a + b)) hsum
    exact IdealImDirect (by rw [← hA]; exact hw)
  have hdif : a - b = 0 := by
    have key : (1 - X) * (1 + Y) * (TT - 1) * (a - b) = 0 := by
      have h3 : (1 - X) * (A * (a - b)) = -((1 - X) * (1 + Y) * (TT - 1) * (a - b)) := by
        rw [hA]
        calc (1 - X) * ((TT - 1) ^ 2 * (a - b))
            = (1 - X) * ((TT - 1) * ((TT - 1) * (a - b))) := by rw [pow_two, mul_assoc]
          _ = ((1 - X) * (TT - 1)) * ((TT - 1) * (a - b)) := by rw [mul_assoc]
          _ = (-((1 - X) * (1 + Y))) * ((TT - 1) * (a - b)) := by rw [one_sub_X_mul_TT_sub_one]
          _ = -(((1 - X) * (1 + Y)) * (TT - 1) * (a - b)) := by
              rw [neg_mul]; simp only [mul_assoc]
      have h4 : -((1 - X) * (1 + Y) * (TT - 1) * (a - b)) = 0 := by rw [← h3]; exact hdiff
      exact neg_eq_zero.mp h4
    exact Ip_torsion key
  have ha : a = 0 := by
    have h4 : (2 : ℂ) • a = 0 := by
      have h5 : (2 : ℂ) • a = a + b + (a - b) := by rw [two_smul]; abel
      rw [h5, hab, hdif, add_zero]
    have h6 := congrArg (fun x : RR => (2⁻¹ : ℂ) • x) h4
    simpa [smul_smul] using h6
  have hb : b = 0 := by rw [ha, zero_add] at hab; exact hab
  exact ⟨ha, hb⟩

end

end Work.FreeProduct
