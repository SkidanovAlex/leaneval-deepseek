import Mathlib
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.Tools
import Submission.Work.FreeProduct.orbit_corollary
import Submission.Work.FreeProduct.T_zpow_injective
import Submission.Work.FreeProduct.Decomp
import Submission.Work.FreeProduct.LengthFacts


/-!
# Directness of `(T - 1)^2 · R` against `(X - 1) · R`

In the group algebra `RR = ℂ[ℤ/2 ∗ ℤ/3]` with `X` the image of the involution `x = S` and
`T = x * y`, we prove `IdealImDirect`:

`(T - 1)^2 * u = (X - 1) * w  ⟹  u = 0`

i.e. `(T - 1)^2 · RR ∩ (X - 1) · RR = 0`.  This is the directness of `𝓘_-` (CKMRV,
Proposition 3.9), in the free-product picture.  The proof follows the paper:

* Put `v = (T - 1) * u` (so `(T - 1) v = (X - 1) w`).  Multiplying by `X` gives
  `(Y - X) v = -(X - 1) w`, i.e. `(Y - 1) v = (X - 1) (v - w)`, where `Y` is the image of the
  `ℤ/3`-generator `y = ST`.  By `Y_sub_one_mul_eq_zero_of_X_sub_one` (CKMRV Lemma 3.8:
  `(X-1)RR ∩ (Y-1)RR = 0`) it follows that `(Y - 1) v = 0`.
* Hence `Y v = Y2 v = v`, so `MU * v = (1 + Y + Y2) v = 3 v` with `MU = 1 + Y + Y2`; thus
  `v = MU * ((3:ℂ)⁻¹ • v)`.
* `TT_sub_one_mul_eq_zero_of_MU` (CKMRV Corollary 3.6 plus the length computations along the
  orbit of `⟨T⟩`) then gives `(T - 1) u = v = 0`.
* Finally `T - 1` is injective on `RR` (`TT_sub_one_injective`, CKMRV Lemma 3.5), so `u = 0`.

The helpers live in the namespace `Work.FreeProduct.ImDirect`:

* `Y_sub_one_mul_eq_zero_of_X_sub_one` — the intersection `(X-1)RR ∩ (Y-1)RR = 0`,
  via the canonicalisation `exists_NX_canon` of `(X-1) * w` to a coefficient vector whose
  support is `1` or starts with a `ℤ/3`-letter, and the maximal-length coefficient argument
  `MU_mul_X_sub_one_mul_eq_zero`.
* `TT_sub_one_mul_eq_zero_of_MU` — if `(T-1) u = MU * r` then `(T-1) u = 0`, using
  `exists_decomp` (the canonical form `r₀ + x r₁`), `orbit_corollary` (CKMRV Corollary 3.6)
  and the length facts `elen_T_zpow_mul_yx`, `elen_T_zpow_mul_y` along the `T`-orbit.
* `rlen` — the maximal length of a group element occurring in the support of an element of
  the group algebra; `coeff_eq_zero_of_rlen_lt` turns length comparisons into vanishing of
  coefficients.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

namespace ImDirect

/-! ## Section 0: coefficient and length utilities -/

theorem coeff_of_mul' (g δ : FP) (r : RR) :
    MonoidAlgebra.coeff ((MonoidAlgebra.of ℂ FP) g * r) δ = MonoidAlgebra.coeff r (g⁻¹ * δ) := by
  rw [show MonoidAlgebra.of ℂ FP g = MonoidAlgebra.single g (1 : ℂ) from rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  simp

theorem coeff_T_sub_one_mul (u : RR) (δ : FP) :
    MonoidAlgebra.coeff ((TT - 1) * u) δ = MonoidAlgebra.coeff u (T⁻¹ * δ) - MonoidAlgebra.coeff u δ := by
  rw [show (TT : RR) = MonoidAlgebra.of ℂ FP T from rfl, sub_mul, one_mul, MonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, coeff_of_mul']

theorem coeff_ne_zero_of_ne_zero' {r : RR} (h : r ≠ 0) : r.coeff ≠ 0 := by
  intro hc
  exact h (MonoidAlgebra.coeff_inj.mp (by rw [hc, MonoidAlgebra.coeff_zero]))

theorem TT_sub_one_injective (u : RR) (h : (TT - 1) * u = 0) : u = 0 := by
  by_contra hu
  obtain ⟨γ0, hγ0mem⟩ := Finsupp.support_nonempty_iff.mpr (coeff_ne_zero_of_ne_zero' hu)
  have hγ0ne : MonoidAlgebra.coeff u γ0 ≠ 0 := Finsupp.mem_support_iff.mp hγ0mem
  have hcoe : ∀ δ : FP, MonoidAlgebra.coeff u (T⁻¹ * δ) = MonoidAlgebra.coeff u δ := by
    intro δ
    have h1 := coeff_T_sub_one_mul u δ
    rw [h, MonoidAlgebra.coeff_zero] at h1
    exact sub_eq_zero.mp h1.symm
  have hiter : ∀ n : ℤ, MonoidAlgebra.coeff u (T ^ n * γ0) = MonoidAlgebra.coeff u γ0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih =>
      have hT : T⁻¹ * T ^ ((i : ℤ) + 1) = T ^ (i : ℤ) := by
        rw [← zpow_neg_one, ← zpow_add]; ring_nf
      have h2 := hcoe (T ^ ((i : ℤ) + 1) * γ0)
      rw [show T⁻¹ * (T ^ ((i : ℤ) + 1) * γ0) = T ^ (i : ℤ) * γ0 from by
        rw [← mul_assoc, hT]] at h2
      rw [← h2, ih]
    | pred i ih =>
      have hT : T⁻¹ * T ^ (-(i : ℤ)) = T ^ (-(i : ℤ) - 1) := by
        rw [← zpow_neg_one, ← zpow_add]; ring_nf
      have h2 := hcoe (T ^ (-(i : ℤ)) * γ0)
      rw [show T⁻¹ * (T ^ (-(i : ℤ)) * γ0) = T ^ (-(i : ℤ) - 1) * γ0 from by
        rw [← mul_assoc, hT]] at h2
      rw [h2, ih]
  have hinj : Function.Injective (fun n : ℤ => T ^ n * γ0) :=
    fun n m hnm => T_zpow_injective (mul_right_cancel hnm)
  have hinf : (Set.range (fun n : ℤ => T ^ n * γ0)).Infinite := by
    have h := Set.infinite_univ.image (f := fun n : ℤ => T ^ n * γ0)
      (fun a _ b _ hab => hinj hab)
    rwa [Set.image_univ] at h
  refine hinf ((MonoidAlgebra.coeff u).support.finite_toSet.subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hiter n]
  exact hγ0ne

theorem elen_toProd_le (L : List Letter) : elen (toProd L) ≤ L.length := by
  have h := wlen_toProd_smul_le L (Monoid.CoprodI.Word.empty : W)
  have h2 : toProd L • (Monoid.CoprodI.Word.empty : W) = Monoid.CoprodI.Word.equiv (toProd L) := by
    rw [← equiv_one, ← equiv_mul, mul_one]
  rw [h2, wlen] at h
  simpa [wlen, elen] using h

theorem elen_of_le (m : Letter) : elen (Monoid.CoprodI.of m.2) ≤ 1 := by
  have h := wlen_smul_le m.2 (Monoid.CoprodI.Word.empty : W)
  have h2 : Monoid.CoprodI.of m.2 • (Monoid.CoprodI.Word.empty : W) =
      Monoid.CoprodI.Word.equiv (Monoid.CoprodI.of m.2) := by
    rw [← equiv_one, ← equiv_mul, mul_one]
  rw [h2, wlen] at h
  simpa [wlen, elen] using h

theorem elen_x_le : elen x ≤ 1 := by
  have h := elen_toProd_le pX
  rwa [toProd_pX, show pX.length = 1 from rfl] at h

theorem elen_yx_le : elen (y * x) ≤ 2 := by
  have h := elen_toProd_le pYX
  rwa [toProd_pYX, show pYX.length = 2 from rfl] at h

theorem elen_y2x_le : elen (y2 * x) ≤ 2 := by
  have h := elen_toProd_le pY2X
  rwa [toProd_pY2X, show pY2X.length = 2 from rfl] at h

theorem elen_y_le : elen y ≤ 1 := by
  rw [← of_Ly]; exact elen_of_le Ly

theorem elen_y2_le : elen y2 ≤ 1 := by
  rw [← of_Ly2]; exact elen_of_le Ly2

theorem elen_smul_ge (g h : FP) : elen h ≤ elen g + elen (g⁻¹ * h) := by
  conv_lhs => rw [← mul_inv_cancel_left g h]
  exact elen_mul_le g (g⁻¹ * h)

/-! ## Section 0b: elementary group relations -/

theorem y_ne_one : y ≠ 1 := by
  intro h
  have h2 : Monoid.CoprodI.of (M := Cyc) (i := true) (Multiplicative.ofAdd 1 : C3) = 1 := h
  have h1 : (Multiplicative.ofAdd 1 : C3) = 1 :=
    Monoid.CoprodI.of_injective (M := Cyc) (i := true) (by rw [h2, map_one])
  exact absurd h1 (by decide)

theorem y2_ne_one : y2 ≠ 1 := by
  intro h
  apply y_ne_one
  have h2 : y * y = 1 := by rw [← pow_two, ← y2]; exact h
  have h3 : y ^ 3 = y := by
    rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two, h2, one_mul]
  rw [y_cube] at h3
  exact h3.symm

theorem y2_ne_y : y2 ≠ y := by
  intro h
  apply y_ne_one
  have h2 : y * y = y := by rw [← pow_two, ← y2]; exact h
  have h3 : y ^ 3 = y := by
    rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two, h2, h2]
  rw [y_cube] at h3
  exact h3.symm

theorem y2_inv : y2⁻¹ = y := by
  rw [y2, pow_two, mul_inv_rev, y_inv]
  exact y2_mul_y2

theorem y2_mul_left (γ : FP) : y2 * (y2 * γ) = y * γ := by rw [← mul_assoc, y2_mul_y2]

/-! ## Section 1: `rlen`, the maximal length in a support -/

def rlen (r : RR) : ℕ := (MonoidAlgebra.coeff r).support.sup elen

theorem coeff_ne_zero_elen_le {r : RR} {δ : FP} (h : MonoidAlgebra.coeff r δ ≠ 0) :
    elen δ ≤ rlen r :=
  Finset.le_sup (f := elen) (Finsupp.mem_support_iff.mpr h)

theorem coeff_eq_zero_of_rlen_lt {r : RR} {δ : FP} (h : rlen r < elen δ) :
    MonoidAlgebra.coeff r δ = 0 := by
  by_contra hc
  exact absurd (coeff_ne_zero_elen_le hc) (not_le.mpr h)

theorem exists_max_elen {r : RR} (hr : r ≠ 0) :
    ∃ γ : FP, MonoidAlgebra.coeff r γ ≠ 0 ∧ elen γ = rlen r := by
  obtain ⟨γ, hγ, hγ2⟩ := Finset.exists_mem_eq_sup _
    (Finsupp.support_nonempty_iff.mpr (coeff_ne_zero_of_ne_zero' hr)) elen
  exact ⟨γ, Finsupp.mem_support_iff.mp hγ, hγ2.symm⟩

theorem rlen_add_le (r s : RR) : rlen (r + s) ≤ max (rlen r) (rlen s) := by
  rw [rlen, MonoidAlgebra.coeff_add]
  refine Finset.sup_le_iff.mpr ?_
  intro γ hγ
  rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hγ
  rcases eq_or_ne (MonoidAlgebra.coeff r γ) 0 with h | h
  · exact le_trans (coeff_ne_zero_elen_le (by simpa [h] using hγ)) (le_max_right _ _)
  · exact le_trans (coeff_ne_zero_elen_le h) (le_max_left _ _)

theorem rlen_smul_le (c : ℂ) (r : RR) : rlen (c • r) ≤ rlen r := by
  rw [rlen, MonoidAlgebra.coeff_smul]
  refine Finset.sup_le_iff.mpr ?_
  intro γ hγ
  rw [Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hγ
  exact coeff_ne_zero_elen_le (mul_ne_zero_iff.mp hγ).2

theorem rlen_mul_of_le (g : FP) (r : RR) :
    rlen ((MonoidAlgebra.of ℂ FP) g * r) ≤ rlen r + elen g := by
  rw [rlen]
  refine Finset.sup_le_iff.mpr ?_
  intro δ hδ
  rw [Finsupp.mem_support_iff, coeff_of_mul'] at hδ
  have h1 : elen δ ≤ elen g + elen (g⁻¹ * δ) := by
    conv_lhs => rw [← mul_inv_cancel_left g δ]
    exact elen_mul_le g (g⁻¹ * δ)
  have h2 := coeff_ne_zero_elen_le hδ
  omega

theorem rlen_of_le (g : FP) : rlen ((MonoidAlgebra.of ℂ FP) g) ≤ elen g := by
  rw [rlen]
  refine Finset.sup_le_iff.mpr ?_
  intro δ hδ
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single] at hδ
  have h : δ = g := by
    have := Finsupp.support_single_subset hδ
    simpa using this
  rw [h]

theorem rlen_one : rlen (1 : RR) = 0 := by
  have h : (1 : RR) = MonoidAlgebra.of ℂ FP (1 : FP) := (map_one _).symm
  rw [h]
  exact le_antisymm (le_trans (rlen_of_le (1 : FP)) (le_of_eq elen_one)) (Nat.zero_le _)

theorem rlen_MU_le : rlen MU ≤ 1 := by
  have h1 : rlen (1 : RR) ≤ 1 := by rw [rlen_one]; norm_num
  have h2 : rlen Y ≤ 1 := le_trans (rlen_of_le y) elen_y_le
  have h3 : rlen Y2 ≤ 1 := le_trans (rlen_of_le y2) elen_y2_le
  calc rlen MU ≤ max (rlen (1 + Y)) (rlen Y2) := by rw [MU]; exact rlen_add_le _ _
    _ ≤ max (max (rlen (1:RR)) (rlen Y)) (rlen Y2) := max_le_max (rlen_add_le _ _) le_rfl
    _ ≤ 1 := max_le (max_le h1 h2) h3

/-! ## Section 1b: coefficients of the basis elements -/

theorem coeff_single_apply (g δ : FP) (c : ℂ) :
    MonoidAlgebra.coeff (MonoidAlgebra.single g c : RR) δ = if δ = g then c else 0 := by
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : δ = g
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

theorem coeff_one_apply (δ : FP) : MonoidAlgebra.coeff (1 : RR) δ = if δ = 1 then 1 else 0 := by
  rw [show (1 : RR) = MonoidAlgebra.single (1:FP) (1:ℂ) from MonoidAlgebra.one_def]
  exact coeff_single_apply 1 δ 1

theorem coeff_MU (δ : FP) :
    MonoidAlgebra.coeff MU δ =
      (if δ = 1 then 1 else 0) + (if δ = y then 1 else 0) + (if δ = y2 then 1 else 0) := by
  rw [MU, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply,
    coeff_one_apply]
  rw [show (Y : RR) = MonoidAlgebra.single y (1:ℂ) from rfl, coeff_single_apply,
    show (Y2 : RR) = MonoidAlgebra.single y2 (1:ℂ) from rfl, coeff_single_apply]

theorem coeff_MU_y : MonoidAlgebra.coeff MU y = 1 := by
  rw [coeff_MU]
  simp only [if_neg y_ne_one, if_neg (Ne.symm y2_ne_y)]
  norm_num

/-! ## Section 2: the intersection `(X-1)R ∩ (Y-1)R = 0` -/

theorem inv_y2x_mul (γ : FP) : (y2 * x)⁻¹ * (y2 * x * γ) = γ := by group

theorem inv_yx_mul (γ : FP) : (y * x)⁻¹ * (y2 * x * γ) = x * y * x * γ := by
  rw [show (y * x)⁻¹ = x * y2 by rw [mul_inv_rev, x_inv, y_inv]]
  simp only [mul_assoc]
  rw [y2_mul_left]

theorem inv_x_mul (γ : FP) : x⁻¹ * (y2 * x * γ) = x * y2 * x * γ := by
  rw [x_inv]; group

theorem inv_y2_mul (γ : FP) : y2⁻¹ * (y2 * x * γ) = x * γ := by
  rw [y2_inv, mul_assoc y2 x γ, ← mul_assoc y y2, y_mul_y2, one_mul]

theorem inv_y_mul (γ : FP) : y⁻¹ * (y2 * x * γ) = y * x * γ := by
  rw [y_inv]
  rw [show y2 * (y2 * x * γ) = y2 * (y2 * (x * γ)) by rw [mul_assoc y2 x γ]]
  rw [y2_mul_left]
  rw [mul_assoc y x γ]

theorem coeff_MU_mul_X_sub_one (u : RR) (δ : FP) :
    MonoidAlgebra.coeff (MU * ((X - 1) * u)) δ =
      (MonoidAlgebra.coeff u ((y2*x)⁻¹ * δ) + MonoidAlgebra.coeff u ((y*x)⁻¹ * δ)
        + MonoidAlgebra.coeff u (x⁻¹ * δ)) - MonoidAlgebra.coeff u δ
        - MonoidAlgebra.coeff u (y⁻¹ * δ) - MonoidAlgebra.coeff u (y2⁻¹ * δ) := by
  have hE : MU * ((X - 1) * u) =
      MonoidAlgebra.of ℂ FP (y2*x) * u + MonoidAlgebra.of ℂ FP (y*x) * u
        + MonoidAlgebra.of ℂ FP x * u - MonoidAlgebra.of ℂ FP y2 * u
        - MonoidAlgebra.of ℂ FP y * u - u := by
    have h1 : MonoidAlgebra.of ℂ FP (y2*x) = MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x :=
      map_mul _ _ _
    have h2 : MonoidAlgebra.of ℂ FP (y*x) = MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x :=
      map_mul _ _ _
    rw [h1, h2, MU, X, Y, Y2]
    noncomm_ring
  rw [hE]
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply,
    coeff_of_mul']
  ring

theorem MU_mul_X_sub_one_mul_eq_zero {u : RR}
    (hNX : ∀ γ ∈ (MonoidAlgebra.coeff u).support, NX γ)
    (h : MU * ((X - 1) * u) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨γ, hγc, hγlen⟩ := exists_max_elen hu
  have hNXγ : NX γ := hNX γ (Finsupp.mem_support_iff.mpr hγc)
  have key := coeff_MU_mul_X_sub_one u (y2 * x * γ)
  rw [h, MonoidAlgebra.coeff_zero] at key
  rw [inv_y2x_mul, inv_yx_mul, inv_x_mul, inv_y_mul, inv_y2_mul] at key
  have h0 : MonoidAlgebra.coeff u (x * y * x * γ) = 0 :=
    coeff_eq_zero_of_rlen_lt (by rw [elen_xyx_mul hNXγ, hγlen]; omega)
  have h1 : MonoidAlgebra.coeff u (x * y2 * x * γ) = 0 :=
    coeff_eq_zero_of_rlen_lt (by rw [elen_xy2x_mul hNXγ, hγlen]; omega)
  have h2 : MonoidAlgebra.coeff u (y2 * x * γ) = 0 :=
    coeff_eq_zero_of_rlen_lt (by rw [elen_y2x_mul hNXγ, hγlen]; omega)
  have h3 : MonoidAlgebra.coeff u (y * x * γ) = 0 :=
    coeff_eq_zero_of_rlen_lt (by rw [elen_yx_mul hNXγ, hγlen]; omega)
  have h4 : MonoidAlgebra.coeff u (x * γ) = 0 :=
    coeff_eq_zero_of_rlen_lt (by rw [elen_x_mul hNXγ, hγlen]; omega)
  rw [h0, h1, h2, h3, h4] at key
  simp at key
  exact hγc key.symm

/-! ## Section 3: canonicalisation of `(X-1) * w` to `NX`-supported coefficient vectors -/

theorem exists_NX_of (γ : FP) :
    ∃ u : RR, (X - 1) * u = (X - 1) * MonoidAlgebra.of ℂ FP γ ∧
      ∀ δ ∈ (MonoidAlgebra.coeff u).support, NX δ := by
  by_cases h : NX γ
  · exact ⟨MonoidAlgebra.single γ 1, by rw [MonoidAlgebra.of_apply], by
      intro δ hδ
      have h1 : δ = γ := by
        have := Finsupp.support_single_subset hδ
        simpa using this
      rw [h1]; exact h⟩
  · have hst : (Monoid.CoprodI.Word.equiv γ).fstIdx = some false := by
      rw [NX] at h; exact not_not.mp h
    obtain ⟨γ', hγ', hNX'⟩ := exists_X_dcomp γ hst
    refine ⟨-(MonoidAlgebra.of ℂ FP γ'), ?_, ?_⟩
    · have h1 : MonoidAlgebra.of ℂ FP γ = X * MonoidAlgebra.of ℂ FP γ' := by
        rw [hγ', map_mul]; rfl
      have h2 : (X - 1) * X = -(X - 1) := by rw [sub_mul, one_mul, X_mul_X]; abel
      rw [h1, ← mul_assoc, h2, neg_mul, mul_neg]
    · intro δ hδ
      have hs : (MonoidAlgebra.coeff (-(MonoidAlgebra.of ℂ FP γ'))).support
          = (MonoidAlgebra.coeff (MonoidAlgebra.of ℂ FP γ')).support := by
        rw [MonoidAlgebra.coeff_neg, Finsupp.support_neg]
      rw [hs] at hδ
      have hs2 : (MonoidAlgebra.coeff (MonoidAlgebra.of ℂ FP γ')).support = {γ'} := by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
        exact Finsupp.support_single _ one_ne_zero
      rw [hs2] at hδ
      have h2 : δ = γ' := by simpa using hδ
      rw [h2]; exact hNX'

theorem exists_NX_canon (w : RR) :
    ∃ u : RR, (X - 1) * u = (X - 1) * w ∧ ∀ γ ∈ (MonoidAlgebra.coeff u).support, NX γ := by
  classical
  refine MonoidAlgebra.induction_on (R := ℂ) (M := FP)
    (motive := fun y => ∃ y' : RR, (X - 1) * y' = (X - 1) * y ∧
      ∀ γ ∈ (MonoidAlgebra.coeff y').support, NX γ) w ?_ ?_ ?_
  · intro m
    exact exists_NX_of m
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

/-! ## Section 4: length facts along `T`-orbits -/

theorem toList_toProd (l : List Letter) (hne : ∀ a ∈ l, a.2 ≠ 1)
    (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1)) :
    (Monoid.CoprodI.Word.equiv (toProd l)).toList = l := by
  have h := toList_equiv_toProd_mul l (Monoid.CoprodI.Word.empty : W) hne hchain (by
    intro a ha b hb
    simp at hb)
  rw [Monoid.CoprodI.Word.prod_empty, mul_one] at h
  simpa using h

theorem toList_toProd_mul_of_NX (l : List Letter) (hne : ∀ a ∈ l, a.2 ≠ 1)
    (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1)) (hlast : l.getLast? = some Lx)
    {γ : FP} (hNX : NX γ) :
    (Monoid.CoprodI.Word.equiv (toProd l * γ)).toList = l ++ (Monoid.CoprodI.Word.equiv γ).toList := by
  have hjun : ∀ a ∈ l.getLast?, ∀ b ∈ (Monoid.CoprodI.Word.equiv γ).toList.head?, a.1 ≠ b.1 := by
    intro a ha b hb
    rw [hlast] at ha
    have ha' : a = Lx := by rw [Option.mem_some_iff] at ha; exact ha.symm
    subst ha'
    have hb1 : b.1 = true := by
      have h2 : (Monoid.CoprodI.Word.equiv γ).fstIdx = some b.1 := by
        rw [Monoid.CoprodI.Word.fstIdx, hb]; rfl
      cases hb' : b.1
      · exact absurd (show (Monoid.CoprodI.Word.equiv γ).fstIdx = some false by rw [h2, hb']) hNX
      · rfl
    rw [hb1]
    exact (by decide : Lx.1 ≠ true)
  have h := toList_equiv_toProd_mul l (Monoid.CoprodI.Word.equiv γ) hne hchain hjun
  rwa [prod_equiv] at h

def pXY2 : List Letter := [Lx, Ly2]
def pY2XY : List Letter := [Ly2, Lx, Ly]
def pY2XYX : List Letter := [Ly2, Lx, Ly, Lx]

@[simp] theorem toProd_pXY2 : toProd pXY2 = x * y2 := by
  rw [pXY2, toProd_cons, toProd_cons, toProd_nil, mul_one, of_Lx, of_Ly2]

@[simp] theorem toProd_pY2XY : toProd pY2XY = y2 * x * y := by
  rw [pY2XY, toProd_cons, toProd_cons, toProd_cons, toProd_nil, mul_one, of_Ly2, of_Lx, of_Ly]
  group

@[simp] theorem toProd_pY2XYX : toProd pY2XYX = y2 * x * y * x := by
  rw [pY2XYX, toProd_cons, toProd_cons, toProd_cons, toProd_cons, toProd_nil, mul_one,
    of_Ly2, of_Lx, of_Ly]
  group

theorem toList_xy2 : (Monoid.CoprodI.Word.equiv (x * y2)).toList = pXY2 := by
  have h := toList_toProd pXY2 (by decide) (by decide)
  rwa [toProd_pXY2] at h

theorem elen_xy2 : elen (x * y2) = 2 := by rw [elen, wlen, toList_xy2]; rfl

theorem startsLx_xy2 : StartsLx (x * y2) := by rw [StartsLx, toList_xy2]; rfl

theorem toList_y2xy : (Monoid.CoprodI.Word.equiv (y2 * x * y)).toList = pY2XY := by
  have h := toList_toProd pY2XY (by decide) (by decide)
  rwa [toProd_pY2XY] at h

theorem elen_y2xy : elen (y2 * x * y) = 3 := by rw [elen, wlen, toList_y2xy]; rfl

theorem startsLy2_y2xy : StartsLy2 (y2 * x * y) := by rw [StartsLy2, toList_y2xy]; rfl

theorem toList_xy2x_mul {γ : FP} (hNX : NX γ) :
    (Monoid.CoprodI.Word.equiv (x * y2 * x * γ)).toList =
      pXY2X ++ (Monoid.CoprodI.Word.equiv γ).toList := by
  have h := toList_toProd_mul_of_NX pXY2X (by decide) (by decide)
    (rfl : pXY2X.getLast? = some Lx) hNX
  rwa [toProd_pXY2X] at h

theorem startsLx_xy2x_mul {γ : FP} (hNX : NX γ) : StartsLx (x * y2 * x * γ) := by
  rw [StartsLx, toList_xy2x_mul hNX]; rfl

theorem toList_y2xyx_mul {γ : FP} (hNX : NX γ) :
    (Monoid.CoprodI.Word.equiv (y2 * x * y * x * γ)).toList =
      pY2XYX ++ (Monoid.CoprodI.Word.equiv γ).toList := by
  have h := toList_toProd_mul_of_NX pY2XYX (by decide) (by decide)
    (rfl : pY2XYX.getLast? = some Lx) hNX
  rwa [toProd_pY2XYX] at h

theorem elen_y2xyx_mul {γ : FP} (hNX : NX γ) : elen (y2 * x * y * x * γ) = elen γ + 4 := by
  have h' := elen_toProd_mul_of_fstIdx pY2XYX Lx (Monoid.CoprodI.Word.equiv γ) (by decide) (by decide)
    (rfl : pY2XYX.getLast? = some Lx) (by simpa [NX] using hNX)
  rw [toProd_pY2XYX, wlen_equiv] at h'
  have hl : pY2XYX.length = 4 := rfl
  simpa [hl, Nat.add_comm 4 (elen γ), prod_equiv] using h'

theorem startsLy2_y2xyx_mul {γ : FP} (hNX : NX γ) : StartsLy2 (y2 * x * y * x * γ) := by
  rw [StartsLy2, toList_y2xyx_mul hNX]; rfl

theorem T_mul_yx (γ : FP) : T * (y * x * γ) = x * y2 * x * γ := by
  rw [T, show y2 = y * y from (pow_two y).symm]
  group

theorem Tinv_mul_yx (γ : FP) : T⁻¹ * (y * x * γ) = y2 * x * y * x * γ := by
  rw [Tinv_eq]
  group

theorem T_mul_y : T * y = x * y2 := by
  rw [T, show y2 = y * y from (pow_two y).symm]
  group

theorem Tinv_mul_y : T⁻¹ * y = y2 * x * y := by rw [Tinv_eq]

theorem len_T_pow_mul_yx (γ : FP) (hNX : NX γ) :
    ∀ n : ℕ, elen (T ^ (n + 1) * (y * x * γ)) = elen γ + 2 * (n + 1) + 1 ∧
      StartsLx (T ^ (n + 1) * (y * x * γ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Nat.zero_add, pow_one, T_mul_yx, elen_xy2x_mul hNX]
    · rw [Nat.zero_add, pow_one, T_mul_yx]; exact startsLx_xy2x_mul hNX
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ', mul_assoc, T_mul_elen ih.2, ih.1]; ring
    · rw [pow_succ', mul_assoc]; exact T_mul_startsLx ih.2

theorem len_Tinv_pow_mul_yx (γ : FP) (hNX : NX γ) :
    ∀ k : ℕ, elen ((T⁻¹) ^ (k + 1) * (y * x * γ)) = elen γ + 2 * (k + 1) + 2 ∧
      StartsLy2 ((T⁻¹) ^ (k + 1) * (y * x * γ)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Nat.zero_add, pow_one, Tinv_mul_yx, elen_y2xyx_mul hNX]
    · rw [Nat.zero_add, pow_one, Tinv_mul_yx]; exact startsLy2_y2xyx_mul hNX
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ', mul_assoc, Tinv_mul_elen ih.2, ih.1]; ring
    · rw [pow_succ', mul_assoc]; exact Tinv_mul_startsLy2 ih.2

theorem len_T_pow_mul_y :
    ∀ n : ℕ, elen (T ^ (n + 1) * y) = 2 * (n + 1) ∧ StartsLx (T ^ (n + 1) * y) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Nat.zero_add, pow_one, T_mul_y, elen_xy2]
    · rw [Nat.zero_add, pow_one, T_mul_y]; exact startsLx_xy2
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ', mul_assoc, T_mul_elen ih.2, ih.1]; ring
    · rw [pow_succ', mul_assoc]; exact T_mul_startsLx ih.2

theorem len_Tinv_pow_mul_y :
    ∀ k : ℕ, elen ((T⁻¹) ^ (k + 1) * y) = 2 * (k + 1) + 1 ∧ StartsLy2 ((T⁻¹) ^ (k + 1) * y) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Nat.zero_add, pow_one, Tinv_mul_y, elen_y2xy]
    · rw [Nat.zero_add, pow_one, Tinv_mul_y]; exact startsLy2_y2xy
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ', mul_assoc, Tinv_mul_elen ih.2, ih.1]; ring
    · rw [pow_succ', mul_assoc]; exact Tinv_mul_startsLy2 ih.2

theorem elen_T_zpow_mul_yx {γ : FP} (hNX : NX γ) {n : ℤ} (hn : n ≠ 0) :
    elen γ + 3 ≤ elen (T ^ n * (y * x * γ)) := by
  rcases Int.eq_nat_or_neg n with ⟨k, hk | hk⟩
  · subst hk
    rw [zpow_natCast]
    have hk0 : k ≠ 0 := by rintro rfl; exact hn (by norm_num)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [(len_T_pow_mul_yx γ hNX k').1]
    omega
  · subst hk
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    have hk0 : k ≠ 0 := by rintro rfl; exact hn (by norm_num)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [(len_Tinv_pow_mul_yx γ hNX k').1]
    omega

theorem elen_T_zpow_mul_y {n : ℤ} (hn : n ≠ 0) : 2 ≤ elen (T ^ n * y) := by
  rcases Int.eq_nat_or_neg n with ⟨k, hk | hk⟩
  · subst hk
    rw [zpow_natCast]
    have hk0 : k ≠ 0 := by rintro rfl; exact hn (by norm_num)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [(len_T_pow_mul_y k').1]
    omega
  · subst hk
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    have hk0 : k ≠ 0 := by rintro rfl; exact hn (by norm_num)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [(len_Tinv_pow_mul_y k').1]
    omega

/-! ## Section 4c: group identities at `y * x * γ` -/

theorem inv_yx_mul_yx (γ : FP) : (y * x)⁻¹ * (y * x * γ) = γ := by group

theorem inv_x_mul_yx (γ : FP) : x⁻¹ * (y * x * γ) = x * y * x * γ := by
  rw [x_inv]; group

theorem inv_y2x_mul_yx (γ : FP) : (y2 * x)⁻¹ * (y * x * γ) = x * y2 * x * γ := by
  rw [show (y2 * x)⁻¹ = x * y by rw [mul_inv_rev, y2_inv, x_inv]]
  rw [show x * y * (y * x * γ) = x * (y * (y * (x * γ))) by simp only [mul_assoc]]
  rw [← mul_assoc y y (x * γ), ← pow_two, ← y2]
  simp only [mul_assoc]

/-! ## Section 4b: coefficient identity for the canonical form -/

theorem coeff_MU_mul_canon (r₀ : ℂ) (r₁ : RR) (δ : FP) :
    MonoidAlgebra.coeff (MU * (MonoidAlgebra.single (1:FP) r₀ + X * r₁)) δ =
      MonoidAlgebra.coeff MU δ * r₀ + MonoidAlgebra.coeff r₁ (x⁻¹ * δ)
        + MonoidAlgebra.coeff r₁ ((y*x)⁻¹ * δ) + MonoidAlgebra.coeff r₁ ((y2*x)⁻¹ * δ) := by
  have h1 : MonoidAlgebra.coeff (MU * MonoidAlgebra.single (1:FP) r₀) δ =
      MonoidAlgebra.coeff MU δ * r₀ := by
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  have hX : MU * X = MonoidAlgebra.of ℂ FP x + MonoidAlgebra.of ℂ FP (y*x)
      + MonoidAlgebra.of ℂ FP (y2*x) := by
    have h2 : MonoidAlgebra.of ℂ FP (y*x) = MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x :=
      map_mul _ _ _
    have h3 : MonoidAlgebra.of ℂ FP (y2*x) = MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x :=
      map_mul _ _ _
    rw [h2, h3, MU, X, Y, Y2]
    noncomm_ring
  have h2 : MonoidAlgebra.coeff (MU * X * r₁) δ = MonoidAlgebra.coeff r₁ (x⁻¹ * δ)
      + MonoidAlgebra.coeff r₁ ((y*x)⁻¹ * δ) + MonoidAlgebra.coeff r₁ ((y2*x)⁻¹ * δ) := by
    rw [hX, add_mul, add_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_of_mul']
  rw [mul_add, ← mul_assoc, MonoidAlgebra.coeff_add, Finsupp.add_apply, h1, h2]
  ring

/-! ## Section 5: `(T-1) u ∈ MU * R` implies `(T-1) u = 0` -/

theorem TT_sub_one_mul_eq_zero_of_MU (u r : RR) (h : (TT - 1) * u = MU * r) :
    (TT - 1) * u = 0 := by
  obtain ⟨r₀, r₁, hdec, hNX⟩ := exists_decomp r
  have hw : (TT - 1) * u = MU * (MonoidAlgebra.single (1:FP) r₀ + X * r₁) := by rw [h, hdec]
  by_cases hr₁ : r₁ = 0
  · subst hr₁
    rw [mul_zero, add_zero] at hw
    by_cases hr₀ : r₀ = 0
    · rw [hr₀, MonoidAlgebra.single_zero, mul_zero] at hw
      exact hw
    · have hcontra : False := by
        refine orbit_corollary T_zpow_injective (w := (TT-1)*u) (u := u) (γ := y)
          (c := r₀) rfl ?_ hr₀ ?_
        · rw [hw, MonoidAlgebra.coeff_mul_single_apply]
          simp [coeff_MU_y]
        · intro n hn
          rw [hw, MonoidAlgebra.coeff_mul_single_apply]
          have hMU := rlen_MU_le
          have h3 := elen_T_zpow_mul_y hn
          have h2 : MonoidAlgebra.coeff MU (T ^ n * y) = 0 :=
            coeff_eq_zero_of_rlen_lt (by omega)
          rw [show (T ^ n * y) * 1⁻¹ = T ^ n * y by rw [inv_one, mul_one], h2, zero_mul]
      exact hcontra.elim
  · obtain ⟨γ, hγc, hγlen⟩ := exists_max_elen hr₁
    have hNXγ : NX γ := hNX γ (Finsupp.mem_support_iff.mpr hγc)
    have hcontra : False := by
      refine orbit_corollary T_zpow_injective (w := (TT-1)*u) (u := u) (γ := y * x * γ)
        (c := MonoidAlgebra.coeff r₁ γ) rfl ?_ hγc ?_
      · rw [hw, coeff_MU_mul_canon, inv_x_mul_yx, inv_yx_mul_yx, inv_y2x_mul_yx]
        have hMU := rlen_MU_le
        have hδ : MonoidAlgebra.coeff MU (y * x * γ) = 0 :=
          coeff_eq_zero_of_rlen_lt (by rw [elen_yx_mul hNXγ]; omega)
        have hx : MonoidAlgebra.coeff r₁ (x * y * x * γ) = 0 :=
          coeff_eq_zero_of_rlen_lt (by rw [elen_xyx_mul hNXγ, hγlen]; omega)
        have hx2 : MonoidAlgebra.coeff r₁ (x * y2 * x * γ) = 0 :=
          coeff_eq_zero_of_rlen_lt (by rw [elen_xy2x_mul hNXγ, hγlen]; omega)
        rw [hδ, hx, hx2, zero_mul, zero_add, zero_add]
        ring
      · intro n hn
        rw [hw, coeff_MU_mul_canon]
        have hMU := rlen_MU_le
        have hδ : MonoidAlgebra.coeff MU (T ^ n * (y * x * γ)) = 0 :=
          coeff_eq_zero_of_rlen_lt (by have h3 := elen_T_zpow_mul_yx hNXγ hn; omega)
        have hx : MonoidAlgebra.coeff r₁ (x⁻¹ * (T ^ n * (y * x * γ))) = 0 :=
          coeff_eq_zero_of_rlen_lt (by
            have h1 := elen_smul_ge x (T ^ n * (y * x * γ))
            have h2 := elen_T_zpow_mul_yx hNXγ hn
            have h3 := elen_x_le
            rw [← hγlen]; omega)
        have hyx : MonoidAlgebra.coeff r₁ ((y*x)⁻¹ * (T ^ n * (y * x * γ))) = 0 :=
          coeff_eq_zero_of_rlen_lt (by
            have h1 := elen_smul_ge (y * x) (T ^ n * (y * x * γ))
            have h2 := elen_T_zpow_mul_yx hNXγ hn
            have h3 := elen_yx_le
            rw [← hγlen]; omega)
        have hy2x : MonoidAlgebra.coeff r₁ ((y2*x)⁻¹ * (T ^ n * (y * x * γ))) = 0 :=
          coeff_eq_zero_of_rlen_lt (by
            have h1 := elen_smul_ge (y2 * x) (T ^ n * (y * x * γ))
            have h2 := elen_T_zpow_mul_yx hNXγ hn
            have h3 := elen_y2x_le
            rw [← hγlen]; omega)
        rw [hδ, hx, hyx, hy2x, zero_mul, zero_add, zero_add, zero_add]
    exact hcontra.elim


theorem Y_sub_one_mul_eq_zero_of_X_sub_one (v w : RR) (h : (Y - 1) * v = (X - 1) * w) :
    (Y - 1) * v = 0 := by
  obtain ⟨u, hu, hNX⟩ := exists_NX_canon w
  have hMU0 : MU * ((X - 1) * u) = 0 := by
    rw [hu, ← h]
    show MU * ((Y - 1) * v) = 0
    rw [← mul_assoc, mul_sub, mul_one, MU_mul_Y, sub_self, zero_mul]
  have hu0 : u = 0 := MU_mul_X_sub_one_mul_eq_zero hNX hMU0
  calc (Y - 1) * v = (X - 1) * w := h
    _ = (X - 1) * u := hu.symm
    _ = (X - 1) * 0 := by rw [hu0]
    _ = 0 := mul_zero _

end ImDirect

theorem IdealImDirect {u w : Work.FreeProduct.RR}
    (h : (Work.FreeProduct.TT - 1) ^ 2 * u = (Work.FreeProduct.X - 1) * w) : u = 0:= by
  set v : RR := (TT - 1) * u with hv
  have hv2 : (TT - 1) * v = (X - 1) * w := by
    rw [hv, ← h, pow_two, mul_assoc]
  have hX1 : X * (X - 1) = -(X - 1) := by rw [mul_sub, mul_one, X_mul_X]; abel
  have hXT : X * (TT - 1) = Y - X := by
    rw [mul_sub, mul_one, show X * TT = Y from by rw [← X_mul_Y, ← mul_assoc, X_mul_X, one_mul]]
  have hc : (Y - 1) * v = (X - 1) * (v - w) := by
    have hA : X * ((TT - 1) * v) = (Y - X) * v := by rw [← mul_assoc, hXT]
    have hB : X * ((X - 1) * w) = -((X - 1) * w) := by rw [← mul_assoc, hX1, neg_mul]
    have h1 : (Y - X) * v = -((X - 1) * w) := by
      have := congrArg (fun z => X * z) hv2
      rwa [hA, hB] at this
    calc (Y - 1) * v = (X - 1) * v + (Y - X) * v := by rw [← add_mul]; abel
      _ = (X - 1) * v + (-((X - 1) * w)) := by rw [h1]
      _ = (X - 1) * (v - w) := by rw [mul_sub]; abel
  have hY : (Y - 1) * v = 0 := ImDirect.Y_sub_one_mul_eq_zero_of_X_sub_one v (v - w) hc
  have hYv : Y * v = v := by
    have h1 := hY
    rw [sub_mul, one_mul] at h1
    exact sub_eq_zero.mp h1
  have hY2v : Y2 * v = v := by rw [← Y_mul_Y, mul_assoc, hYv, hYv]
  have h3 : (3:ℂ) • v = v + v + v := by
    rw [Algebra.smul_def, show (algebraMap ℂ RR) (3:ℂ) = (3:RR) from map_ofNat _ 3]
    rw [show (3:RR) = 2 + 1 from by norm_num, add_mul, two_mul, one_mul]
  have hMUv : MU * v = (3:ℂ) • v := by
    rw [h3, MU, add_mul, add_mul, one_mul, hYv, hY2v]
  have hv_eq : (3:ℂ)⁻¹ • (MU * v) = v := by
    rw [hMUv, smul_smul, inv_mul_cancel₀ (by norm_num : (3:ℂ) ≠ 0), one_smul]
  have h0 : (TT - 1) * u = 0 := by
    have hh : (TT - 1) * u = MU * ((3:ℂ)⁻¹ • v) := by rw [mul_smul_comm, hv_eq, hv]
    exact ImDirect.TT_sub_one_mul_eq_zero_of_MU u ((3:ℂ)⁻¹ • v) hh
  exact ImDirect.TT_sub_one_injective u h0



end

end Work.FreeProduct
