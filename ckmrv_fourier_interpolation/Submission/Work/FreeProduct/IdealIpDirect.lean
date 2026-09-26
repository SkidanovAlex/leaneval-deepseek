import Mathlib
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.Tools
import Submission.Work.FreeProduct.orbit_corollary
import Submission.Work.FreeProduct.T_zpow_injective
import Submission.Work.FreeProduct.Canonical
import Submission.Work.FreeProduct.Decomp
import Submission.Work.FreeProduct.LengthFacts

/-!
# Directness of `(T - 1)^2 · R` against `(X + 1) · R` (the CKMRV ideal `𝓘₊`)

Main result (`Work.FreeProduct.IdealIpDirect`):

  `(T - 1)^2 * u = (X + 1) * w  →  u = 0`

in the group algebra `RR = ℂ[ℤ/2 ∗ ℤ/3]`, where `X` is the image of the involution `x = S` and
`T = x * y` (`y = ST`).  Equivalently `(X + 1)·RR ∩ (T - 1)^2·RR = 0`.

The proof follows CKMRV, Proposition 3.1/prop:freeideals1, for the ideal `𝓘₊`:

* with `v = (T - 1) * u` the hypothesis reads `(T - 1) * v ∈ (X + 1)·RR`; since
  `T - 1 = (X + 1) * Y - (Y + 1)` and `Y + 1` is a unit (inverse `(Y² - Y + 1)/2`), this forces
  `v = (Y² - Y + 1) * (X + 1) * r` for some `r` (CKMRV Lemma 3.7);
* every element `r` can be written (modulo the kernel `(X - 1)·RR` of left multiplication by
  `Y² - Y + 1`) as `c·1 + Y·r₁ + Y²·r₂` with `r₁, r₂` supported on elements that are `1` or start
  with `x` (`XF`);
* expanding `(Y² - Y + 1)(X + 1)(c + Y r₁ + Y² r₂)` into its `18` monomials shows that for a
  suitable `δ` (built from an element of maximal length in the support of `r₂`, resp. `r₁`) the
  coefficient of `δ` in `v` is nonzero while all its nonzero `⟨T⟩`-translates are strictly longer
  than any element of the support of `v`, so have zero coefficient.  The orbit corollary
  (CKMRV Corollary 3.4) then contradicts `v ∈ (T - 1)·RR`.

Hence `v = 0`, and `T - 1` is injective.

All auxiliary material lives in the namespace `Work.FreeProduct.IpDirect`.
-/

set_option maxRecDepth 8000

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

namespace IpDirect

/-! ## 1. Word lemmas for elements whose reduced word is `1` or starts with `x` -/

/-- If `l` is a reduced list of letters whose last letter lies in the `ℤ/3`-factor, then
prepending it to an `XF` element concatenates the reduced words. -/
theorem toList_toProd_mul_of_XF {l : List Letter} {z : FP}
    (hne : ∀ a ∈ l, a.2 ≠ 1)
    (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1))
    (hlast : ∀ a ∈ l.getLast?, a.1 = true)
    (hz : XF z) :
    (Monoid.CoprodI.Word.equiv (toProd l * z)).toList
      = l ++ (Monoid.CoprodI.Word.equiv z).toList := by
  have h' := toList_equiv_toProd_mul l (Monoid.CoprodI.Word.equiv z) hne hchain (by
    intro a ha b hb
    have hb' : b.1 ≠ true := (Monoid.CoprodI.Word.fstIdx_ne_iff.mp hz b hb).symm
    intro hcon
    exact hb' (by rw [← hcon, hlast a ha]))
  rwa [prod_equiv] at h'

/-- The length of such a concatenation is the sum of the lengths. -/
theorem elen_toProd_mul_of_XF {l : List Letter} {z : FP}
    (hne : ∀ a ∈ l, a.2 ≠ 1)
    (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1))
    (hlast : ∀ a ∈ l.getLast?, a.1 = true)
    (hz : XF z) : elen (toProd l * z) = l.length + elen z := by
  show (Monoid.CoprodI.Word.equiv (toProd l * z)).toList.length
      = l.length + (Monoid.CoprodI.Word.equiv z).toList.length
  rw [toList_toProd_mul_of_XF hne hchain hlast hz, List.length_append]

/-- If moreover the first letter of `l` lies in the `ℤ/3`-factor, the product is not `XF`. -/
theorem not_XF_toProd_mul {l : List Letter} {z : FP} (hl : l ≠ [])
    (hne : ∀ a ∈ l, a.2 ≠ 1)
    (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1))
    (hhead : ∀ a ∈ l.head?, a.1 = true)
    (hlast : ∀ a ∈ l.getLast?, a.1 = true)
    (hz : XF z) : ¬ XF (toProd l * z) := by
  intro hcon
  have h1 := toList_toProd_mul_of_XF hne hchain hlast hz
  obtain ⟨a, ha⟩ : ∃ a, l.head? = some a := by
    cases h : l with
    | nil => exact absurd h hl
    | cons b t => exact ⟨b, rfl⟩
  have h2 : (Monoid.CoprodI.Word.equiv (toProd l * z)).fstIdx = some true := by
    rw [Monoid.CoprodI.Word.fstIdx, h1, List.head?_append_of_ne_nil l hl, ha]
    exact congrArg some (hhead a ha)
  exact hcon h2

theorem toProd_xy_eq : toProd [Lx, Ly] = x * y := by
  rw [toProd_cons, toProd_cons, toProd_nil, mul_one, of_Lx, of_Ly]

theorem toProd_xy2_eq : toProd [Lx, Ly2] = x * y2 := by
  rw [toProd_cons, toProd_cons, toProd_nil, mul_one, of_Lx, of_Ly2]

/-- Prepending `x * y` to an `XF` element adds exactly `2` to the length. -/
theorem elen_xy_mul_of_XF {z : FP} (hz : XF z) : elen (x * y * z) = elen z + 2 := by
  have h := elen_toProd_mul_of_XF (l := [Lx, Ly]) (z := z) (by decide) (by decide) (by decide) hz
  rw [toProd_xy_eq] at h
  simpa [Nat.add_comm] using h

/-- Prepending `x * y²` to an `XF` element adds exactly `2` to the length. -/
theorem elen_xy2_mul_of_XF {z : FP} (hz : XF z) : elen (x * y2 * z) = elen z + 2 := by
  have h := elen_toProd_mul_of_XF (l := [Lx, Ly2]) (z := z) (by decide) (by decide) (by decide) hz
  rw [toProd_xy2_eq] at h
  simpa [Nat.add_comm] using h

/-- `x * y * z` is `XF` when `z` is. -/
theorem XF_xy_mul_of_XF {z : FP} (hz : XF z) : XF (x * y * z) := by
  have h := toList_toProd_mul_of_XF (l := [Lx, Ly]) (z := z) (by decide) (by decide) (by decide) hz
  rw [toProd_xy_eq] at h
  rw [XF, Monoid.CoprodI.Word.fstIdx, h]
  simp

/-- `x * y² * z` is `XF` when `z` is. -/
theorem XF_xy2_mul_of_XF {z : FP} (hz : XF z) : XF (x * y2 * z) := by
  have h := toList_toProd_mul_of_XF (l := [Lx, Ly2]) (z := z) (by decide) (by decide) (by decide) hz
  rw [toProd_xy2_eq] at h
  rw [XF, Monoid.CoprodI.Word.fstIdx, h]
  simp

/-! ## 2. The element `q = (Y² - Y + 1)(X + 1)` -/

/-- `q = (Y² - Y + 1) * (X + 1)`. -/
def q : RR := (Y2 - Y + 1) * (X + 1)

/-- `q * Y`, expanded into monomials. -/
def qY : RR := Y2 * X * Y - Y * X * Y + X * Y + 1 - Y2 + Y

/-- `q * Y²`, expanded into monomials. -/
def qY2 : RR := Y2 * X * Y2 - Y * X * Y2 + X * Y2 + Y - 1 + Y2

theorem q_mul_Y : (q : RR) * Y = qY := by
  have hY : (Y : RR) * Y = Y2 := Y_mul_Y
  have hY2 : (Y2 : RR) * Y = 1 := Y2_mul_Y
  rw [q, qY]
  rw [show (Y2 - Y + 1 : RR) * (X + 1) * Y = (Y2 - Y + 1) * (X * Y + Y) from by noncomm_ring]
  rw [show (Y2 - Y + 1 : RR) * (X * Y + Y)
      = Y2 * (X * Y) + Y2 * Y - Y * (X * Y) - Y * Y + X * Y + Y from by noncomm_ring]
  rw [hY, hY2]
  noncomm_ring

theorem q_mul_Y2 : (q : RR) * Y2 = qY2 := by
  have hY : (Y : RR) * Y2 = 1 := Y_mul_Y2
  have hY2 : (Y2 : RR) * Y2 = Y := Y2_mul_Y2
  rw [q, qY2]
  rw [show (Y2 - Y + 1 : RR) * (X + 1) * Y2 = (Y2 - Y + 1) * (X * Y2 + Y2) from by noncomm_ring]
  rw [show (Y2 - Y + 1 : RR) * (X * Y2 + Y2)
      = Y2 * (X * Y2) + Y2 * Y2 - Y * (X * Y2) - Y * Y2 + X * Y2 + Y2 from by noncomm_ring]
  rw [hY, hY2]
  noncomm_ring

/-- `(X + 1)(X - 1) = 0`. -/
theorem X_add_one_mul_X_sub_one : ((X : RR) + 1) * (X - 1) = 0 := by
  rw [add_mul, one_mul, mul_sub, X_mul_X]
  noncomm_ring

/-- The kernel of left multiplication by `q` contains `(X - 1) * RR`. -/
theorem q_mul_X_sub_one : (q : RR) * (X - 1) = 0 := by
  rw [q, mul_assoc, X_add_one_mul_X_sub_one, mul_zero]

/-! ## 3. Coefficients of the expansions -/

theorem coeff_of_mul_Ip (g z : FP) (r : RR) :
    MonoidAlgebra.coeff ((MonoidAlgebra.of ℂ FP) g * r) z = MonoidAlgebra.coeff r (g⁻¹ * z) := by
  rw [show MonoidAlgebra.of ℂ FP g = MonoidAlgebra.single g (1 : ℂ) from rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  simp

/-- The coefficient of `qY * r` expanded into the six monomials of `qY`. -/
theorem coeff_qY_mul (r : RR) (z : FP) :
    MonoidAlgebra.coeff (qY * r) z
      = MonoidAlgebra.coeff r ((y2*x*y)⁻¹ * z) - MonoidAlgebra.coeff r ((y*x*y)⁻¹ * z)
        + MonoidAlgebra.coeff r ((x*y)⁻¹ * z) + MonoidAlgebra.coeff r z
        - MonoidAlgebra.coeff r (y2⁻¹ * z) + MonoidAlgebra.coeff r (y⁻¹ * z) := by
  have e1 : (Y2 * X * Y : RR) = MonoidAlgebra.of ℂ FP (y2 * x * y) := by
    show MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x * MonoidAlgebra.of ℂ FP y = _
    rw [← map_mul, ← map_mul]
  have e2 : (Y * X * Y : RR) = MonoidAlgebra.of ℂ FP (y * x * y) := by
    show MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x * MonoidAlgebra.of ℂ FP y = _
    rw [← map_mul, ← map_mul]
  have e3 : (X * Y : RR) = MonoidAlgebra.of ℂ FP (x * y) := by
    show MonoidAlgebra.of ℂ FP x * MonoidAlgebra.of ℂ FP y = _
    rw [← map_mul]
  have e4 : (Y2 : RR) = MonoidAlgebra.of ℂ FP y2 := rfl
  have e5 : (Y : RR) = MonoidAlgebra.of ℂ FP y := rfl
  rw [qY, e1, e2, e3, e4, e5]
  simp only [sub_mul, add_mul, one_mul, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_add,
    Finsupp.sub_apply, Finsupp.add_apply, coeff_of_mul_Ip]

/-- The coefficient of `qY2 * r` expanded into the six monomials of `qY2`. -/
theorem coeff_qY2_mul (r : RR) (z : FP) :
    MonoidAlgebra.coeff (qY2 * r) z
      = MonoidAlgebra.coeff r ((y2*x*y2)⁻¹ * z) - MonoidAlgebra.coeff r ((y*x*y2)⁻¹ * z)
        + MonoidAlgebra.coeff r ((x*y2)⁻¹ * z) + MonoidAlgebra.coeff r (y⁻¹ * z)
        - MonoidAlgebra.coeff r z + MonoidAlgebra.coeff r (y2⁻¹ * z) := by
  have e1 : (Y2 * X * Y2 : RR) = MonoidAlgebra.of ℂ FP (y2 * x * y2) := by
    show MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x * MonoidAlgebra.of ℂ FP y2 = _
    rw [← map_mul, ← map_mul]
  have e2 : (Y * X * Y2 : RR) = MonoidAlgebra.of ℂ FP (y * x * y2) := by
    show MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x * MonoidAlgebra.of ℂ FP y2 = _
    rw [← map_mul, ← map_mul]
  have e3 : (X * Y2 : RR) = MonoidAlgebra.of ℂ FP (x * y2) := by
    show MonoidAlgebra.of ℂ FP x * MonoidAlgebra.of ℂ FP y2 = _
    rw [← map_mul]
  have e4 : (Y2 : RR) = MonoidAlgebra.of ℂ FP y2 := rfl
  have e5 : (Y : RR) = MonoidAlgebra.of ℂ FP y := rfl
  rw [qY2, e1, e2, e3, e5, e4]
  simp only [sub_mul, add_mul, one_mul, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_add,
    Finsupp.sub_apply, Finsupp.add_apply, coeff_of_mul_Ip]

/-- A monomial `of g` with `g ≠ z` has zero coefficient at `z`. -/
theorem coeff_of_eq_zero_of_ne {g z : FP} (h : g ≠ z) :
    MonoidAlgebra.coeff ((MonoidAlgebra.of ℂ FP) g) z = 0 := by
  rw [show MonoidAlgebra.of ℂ FP g = MonoidAlgebra.single g (1:ℂ) from rfl,
    MonoidAlgebra.coeff_single_apply]
  rw [if_neg]
  exact h

/-- The support of `q` consists of elements of length at most `2`. -/
theorem coeff_q_of_three_le {z : FP} (hz : 3 ≤ elen z) : MonoidAlgebra.coeff (q : RR) z = 0 := by
  have h0 : ∀ g : FP, elen g ≤ 2 → MonoidAlgebra.coeff ((MonoidAlgebra.of ℂ FP) g) z = 0 := by
    intro g hg
    refine coeff_of_eq_zero_of_ne (fun hcon => ?_)
    rw [← hcon] at hz
    omega
  have e1 : (Y2 * X : RR) = MonoidAlgebra.of ℂ FP (y2*x) := by
    show MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x = _; rw [← map_mul]
  have e2 : (Y * X : RR) = MonoidAlgebra.of ℂ FP (y*x) := by
    show MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x = _; rw [← map_mul]
  have e3 : (Y2 : RR) = MonoidAlgebra.of ℂ FP y2 := rfl
  have e4 : (Y : RR) = MonoidAlgebra.of ℂ FP y := rfl
  have e5 : (X : RR) = MonoidAlgebra.of ℂ FP x := rfl
  have e6 : (1 : RR) = MonoidAlgebra.of ℂ FP (1 : FP) := (map_one _).symm
  have expand : ((Y2 - Y + 1 : RR) * (X + 1)) = Y2*X + Y2 - Y*X - Y + X + 1 := by noncomm_ring
  show MonoidAlgebra.coeff (((Y2 - Y + 1) * (X + 1) : RR)) z = 0
  rw [expand, e1, e2, e3, e4, e5, e6]
  simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_add, Finsupp.sub_apply,
    Finsupp.add_apply]
  rw [h0 _ (by decide), h0 _ (by decide), h0 _ (by decide), h0 _ (by decide), h0 _ (by decide),
    h0 _ (by decide)]
  ring


/-! ## 4. The canonical form `c·1 + Y·r₁ + Y²·r₂` modulo `(X - 1)` -/

theorem C3_cases (m : C3) (hm : m ≠ 1) :
    m = Multiplicative.ofAdd 1 ∨ m = Multiplicative.ofAdd 2 := by
  revert m; decide

/-- A reduced word whose first letter is none is empty. -/
theorem eq_one_of_fstIdx_none {z : FP} (h : (Monoid.CoprodI.Word.equiv z).fstIdx = none) :
    z = 1 := by
  have hw : (Monoid.CoprodI.Word.equiv z).toList = (Monoid.CoprodI.Word.empty : W).toList := by
    cases hl : (Monoid.CoprodI.Word.equiv z).toList with
    | nil => rfl
    | cons a t => rw [Monoid.CoprodI.Word.fstIdx, hl] at h; simp at h
  have h1 : Monoid.CoprodI.Word.equiv z = Monoid.CoprodI.Word.empty := Monoid.CoprodI.Word.ext hw
  rw [← prod_equiv z, h1, Monoid.CoprodI.Word.prod_empty]

/-- An `NX` element is `1`, or `y` (resp. `y²`) times an `XF` element. -/
theorem NX_dichotomy {γ : FP} (h : NX γ) :
    γ = 1 ∨ (∃ z : FP, XF z ∧ γ = y * z) ∨ (∃ z : FP, XF z ∧ γ = y2 * z) := by
  by_cases h1 : γ = 1
  · exact Or.inl h1
  · right
    have hf : (Monoid.CoprodI.Word.equiv γ).fstIdx ≠ none := by
      intro hc
      exact h1 (eq_one_of_fstIdx_none hc)
    rcases hfst : (Monoid.CoprodI.Word.equiv γ).fstIdx with _ | i
    · exact absurd hfst hf
    · cases i with
      | false => exact absurd hfst h
      | true =>
        obtain ⟨m, t, h1', h2', hw⟩ := exists_cons_of_fstIdx_eq (i := true) hfst
        have hm := C3_cases m h2'
        have hXF : XF t.prod := by rw [XF, equiv_prod]; exact h1'
        have hγ : γ = Monoid.CoprodI.of (M := Cyc) (i := true) m * t.prod := by
          rw [← Monoid.CoprodI.Word.prod_cons (i := true) m t h2' h1', ← hw, prod_equiv]
        rcases hm with hm | hm
        · subst hm
          exact Or.inl ⟨t.prod, hXF, by rw [hγ, of_C3_one]⟩
        · subst hm
          exact Or.inr ⟨t.prod, hXF, by rw [hγ, of_C3_two]⟩

/-- An `NX` element decomposes into the scalar part and the two `XF`-supported slots. -/
theorem NX_decomp (γ : FP) (a : ℂ) (h : NX γ) :
    ∃ (c : ℂ) (r1 r2 : RR),
      MonoidAlgebra.single γ a = MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2 ∧
      (∀ δ ∈ (MonoidAlgebra.coeff r1).support, XF δ) ∧
      (∀ δ ∈ (MonoidAlgebra.coeff r2).support, XF δ) := by
  rcases NX_dichotomy h with h1 | ⟨z, hz, h2⟩ | ⟨z, hz, h2⟩
  · subst h1
    exact ⟨a, 0, 0, by rw [mul_zero, mul_zero, add_zero, add_zero], by simp, by simp⟩
  · subst h2
    refine ⟨0, MonoidAlgebra.single z a, 0, ?_, ?_, ?_⟩
    · rw [show (Y : RR) = MonoidAlgebra.single y (1 : ℂ) from rfl,
        show (Y2 : RR) = MonoidAlgebra.single y2 (1 : ℂ) from rfl,
        MonoidAlgebra.single_mul_single, one_mul]
      simp
    · intro δ hδ
      have hδz : δ = z := by simpa using Finsupp.support_single_subset hδ
      rw [hδz]; exact hz
    · simp
  · subst h2
    refine ⟨0, 0, MonoidAlgebra.single z a, ?_, ?_, ?_⟩
    · rw [show (Y : RR) = MonoidAlgebra.single y (1 : ℂ) from rfl,
        show (Y2 : RR) = MonoidAlgebra.single y2 (1 : ℂ) from rfl,
        MonoidAlgebra.single_mul_single, one_mul]
      simp
    · simp
    · intro δ hδ
      have hδz : δ = z := by simpa using Finsupp.support_single_subset hδ
      rw [hδz]; exact hz

/-- **The canonical form.**  Every element of `RR` is `c·1 + Y·r₁ + Y²·r₂ + (X - 1)·t` with
`r₁, r₂` supported on elements that are `1` or start with `x`. -/
theorem exists_canon_MUp (r : RR) :
    ∃ (c : ℂ) (r1 r2 t : RR),
      r = MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2 + (X - 1) * t ∧
      (∀ γ ∈ (MonoidAlgebra.coeff r1).support, XF γ) ∧
      (∀ γ ∈ (MonoidAlgebra.coeff r2).support, XF γ) := by
  classical
  refine MonoidAlgebra.induction_on (R := ℂ) (M := FP)
    (motive := fun y => ∃ (c : ℂ) (r1 r2 t : RR),
      y = MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2 + (X - 1) * t ∧
      (∀ γ ∈ (MonoidAlgebra.coeff r1).support, XF γ) ∧
      (∀ γ ∈ (MonoidAlgebra.coeff r2).support, XF γ)) r ?_ ?_ ?_
  · intro m
    by_cases hm : NX m
    · obtain ⟨c, r1, r2, heq, h1, h2⟩ := NX_decomp m 1 hm
      exact ⟨c, r1, r2, 0, by
        rw [show (MonoidAlgebra.of ℂ FP m : RR) = MonoidAlgebra.single m 1 from rfl, heq,
          mul_zero, add_zero], h1, h2⟩
    · have hfst : (Monoid.CoprodI.Word.equiv m).fstIdx = some false := by
        by_contra hc; exact hm hc
      obtain ⟨γ', hmγ', hNX'⟩ := exists_X_dcomp m hfst
      obtain ⟨c, r1, r2, heq, h1, h2⟩ := NX_decomp γ' 1 hNX'
      refine ⟨c, r1, r2, MonoidAlgebra.single γ' (1 : ℂ), ?_, h1, h2⟩
      have hstep : (MonoidAlgebra.single m (1 : ℂ) : RR) = X * MonoidAlgebra.single γ' (1 : ℂ) := by
        rw [hmγ', show (X : RR) = MonoidAlgebra.single x (1 : ℂ) from rfl,
          MonoidAlgebra.single_mul_single, mul_one]
      have hX : (X - 1) * MonoidAlgebra.single γ' (1 : ℂ)
          = MonoidAlgebra.single m (1 : ℂ) - MonoidAlgebra.single γ' (1 : ℂ) := by
        rw [sub_mul, one_mul, hstep]
      rw [show (MonoidAlgebra.of ℂ FP m : RR) = MonoidAlgebra.single m (1 : ℂ) from rfl, hX,
        ← heq]
      abel
  · intro a b ha hb
    obtain ⟨c1, r1, r1b, t1, he1, h1a, h1b⟩ := ha
    obtain ⟨c2, r2, r2b, t2, he2, h2a, h2b⟩ := hb
    refine ⟨c1 + c2, r1 + r2, r1b + r2b, t1 + t2, ?_, ?_, ?_⟩
    · rw [he1, he2, MonoidAlgebra.single_add, mul_add, mul_add, mul_add]
      abel
    · intro γ hγ
      rw [Finsupp.mem_support_iff] at hγ
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply] at hγ
      by_cases h0 : MonoidAlgebra.coeff r1 γ = 0
      · refine h2a γ ?_
        rw [Finsupp.mem_support_iff]
        intro hb0
        exact hγ (by rw [h0, hb0, add_zero])
      · exact h1a γ (Finsupp.mem_support_iff.mpr h0)
    · intro γ hγ
      rw [Finsupp.mem_support_iff] at hγ
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply] at hγ
      by_cases h0 : MonoidAlgebra.coeff r1b γ = 0
      · refine h2b γ ?_
        rw [Finsupp.mem_support_iff]
        intro hb0
        exact hγ (by rw [h0, hb0, add_zero])
      · exact h1b γ (Finsupp.mem_support_iff.mpr h0)
  · intro c a ha
    obtain ⟨c0, r1, r2, t, he, h1, h2⟩ := ha
    refine ⟨c * c0, c • r1, c • r2, c • t, ?_, ?_, ?_⟩
    · rw [he, smul_add, smul_add, smul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm,
        MonoidAlgebra.smul_single, smul_eq_mul]
    · intro γ hγ
      refine h1 γ (Finsupp.mem_support_iff.mpr ?_)
      intro h0
      rw [Finsupp.mem_support_iff] at hγ
      exact hγ (by rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, h0, smul_zero])
    · intro γ hγ
      refine h2 γ (Finsupp.mem_support_iff.mpr ?_)
      intro h0
      rw [Finsupp.mem_support_iff] at hγ
      exact hγ (by rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, h0, smul_zero])

/-! ## 5. Vanishing criteria for coefficients -/

theorem coeff_eq_zero_of_not_XF_supp {r : RR} (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, XF δ)
    {z : FP} (hz : ¬ XF z) : MonoidAlgebra.coeff r z = 0 := by
  by_contra hc
  exact hz (h z (Finsupp.mem_support_iff.mpr hc))

theorem coeff_eq_zero_of_len_supp {r : RR} {N : ℕ}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ N) {z : FP} (hz : N < elen z) :
    MonoidAlgebra.coeff r z = 0 := by
  by_contra hc
  have := h z (Finsupp.mem_support_iff.mpr hc)
  omega

theorem coeff_eq_zero_of_supp_lt {r : RR} {z : FP}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ < elen z) :
    MonoidAlgebra.coeff r z = 0 := by
  by_contra hc
  have := h z (Finsupp.mem_support_iff.mpr hc)
  omega

/-- If all support lengths of `r` are at most `N` and `elen g ≤ M`, then `M + N < elen z`
forces `coeff r (g⁻¹ z) = 0`. -/
theorem coeff_inv_mul_eq_zero_of_long {r : RR} {N M : ℕ}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ N) {g z : FP}
    (hg : elen g ≤ M) (hz : M + N < elen z) : MonoidAlgebra.coeff r (g⁻¹ * z) = 0 := by
  by_contra hc
  have hmem : g⁻¹ * z ∈ (MonoidAlgebra.coeff r).support := Finsupp.mem_support_iff.mpr hc
  have h1 := h _ hmem
  have h2 : elen z ≤ elen g + elen (g⁻¹ * z) := by
    have h3 := elen_mul_le g (g⁻¹ * z)
    rwa [mul_inv_cancel_left] at h3
  omega

/-- The coefficient of `q * (c·1 + Y·r₁ + Y²·r₂)` splits into the three parts. -/
theorem coeff_q_mul_split (c : ℂ) (r1 r2 : RR) (z : FP) :
    MonoidAlgebra.coeff (q * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2)) z
      = c * MonoidAlgebra.coeff (q : RR) z + MonoidAlgebra.coeff (qY * r1) z
        + MonoidAlgebra.coeff (qY2 * r2) z := by
  have hs : (MonoidAlgebra.single (1 : FP) c : RR) = c • (1 : RR) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  have h1 : (q : RR) * MonoidAlgebra.single (1 : FP) c = c • q := by
    rw [hs, mul_smul_comm, mul_one]
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, h1, q_mul_Y, q_mul_Y2]
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-! ## 6. CKMRV Lemma 3.7 and the injectivity of `T - 1` -/

/-- **CKMRV Lemma 3.7.**  `{v : (T - 1) v ∈ (X + 1)·RR} = (Y² - Y + 1)(X + 1)·RR`. -/
theorem mem_qR_of_sub_one_mem {v w : RR} (h : (TT - 1) * v = (X + 1) * w) :
    ∃ r : RR, v = (Y2 - Y + 1) * (X + 1) * r := by
  have hsplit : ((X + 1) * Y - (Y + 1) : RR) = TT - 1 := by
    rw [add_mul, one_mul, X_mul_Y]
    noncomm_ring
  have h2 : (Y + 1) * v = (X + 1) * (Y * v - w) := by
    have h1 : (X + 1) * (Y * v) - (Y + 1) * v = (X + 1) * w := by
      have h0 : ((X + 1) * Y - (Y + 1)) * v = (X + 1) * w := by rw [hsplit]; exact h
      rwa [sub_mul, mul_assoc] at h0
    have hA : (X + 1) * (Y * v) = (X + 1) * w + (Y + 1) * v := sub_eq_iff_eq_add.mp h1
    have hB : (Y + 1) * v = (X + 1) * (Y * v) - (X + 1) * w := by
      rw [hA]; abel
    rw [hB, mul_sub]
  have h4 : (Y2 - Y + 1 : RR) * (Y + 1) = (2 : ℂ) • (1 : RR) := by
    rw [show (Y2 - Y + 1 : RR) * (Y + 1)
        = Y2 * Y + Y2 - Y * Y - Y + Y + 1 from by noncomm_ring]
    rw [Y2_mul_Y, Y_mul_Y, two_smul]
    abel
  have h5 : (2 : ℂ) • v = ((Y2 - Y + 1) * (X + 1)) * (Y * v - w) := by
    calc (2 : ℂ) • v = (((2 : ℂ) • (1 : RR)) * v) := by rw [smul_mul_assoc, one_mul]
      _ = (((Y2 - Y + 1 : RR) * (Y + 1)) * v) := by rw [← h4]
      _ = (Y2 - Y + 1) * ((Y + 1) * v) := by noncomm_ring
      _ = (Y2 - Y + 1) * ((X + 1) * (Y * v - w)) := by rw [h2]
      _ = ((Y2 - Y + 1) * (X + 1)) * (Y * v - w) := by noncomm_ring
  refine ⟨(1 / 2 : ℂ) • (Y * v - w), ?_⟩
  rw [mul_smul_comm, ← h5, smul_smul]
  norm_num

/-- **`T - 1` is injective.**  If `(T - 1) u = 0` then the support of `u` is invariant under left
multiplication by `T`, hence infinite if `u ≠ 0`, contradicting finite support. -/
theorem TT_sub_one_eq_zero {u : RR} (h : (TT - 1) * u = 0) : u = 0 := by
  by_contra hne
  have hcoe : ∀ δ : FP, MonoidAlgebra.coeff u (T⁻¹ * δ) = MonoidAlgebra.coeff u δ := by
    intro δ
    have hw : (0 : RR) = (MonoidAlgebra.of ℂ FP T - 1) * u := by
      rw [← h]; rfl
    have h1 := coeff_sub_one_mul (u := u) (w := (0 : RR)) hw δ
    rw [MonoidAlgebra.coeff_zero] at h1
    exact sub_eq_zero.mp h1.symm
  have hcoe0 : MonoidAlgebra.coeff u ≠ 0 := fun hc => hne (MonoidAlgebra.coeff_eq_zero.mp hc)
  obtain ⟨γ, hγ⟩ := Finsupp.support_nonempty_iff.mpr hcoe0
  have hstep : ∀ δ : FP, MonoidAlgebra.coeff u δ ≠ 0 →
      MonoidAlgebra.coeff u (T * δ) ≠ 0 := by
    intro δ hδ
    have h1 := hcoe (T * δ)
    rw [inv_mul_cancel_left] at h1
    rw [← h1]; exact hδ
  have hmem : ∀ n : ℕ, T ^ n * γ ∈ (MonoidAlgebra.coeff u).support := by
    intro n
    induction n with
    | zero => simpa using hγ
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact Finsupp.mem_support_iff.mpr (hstep _ (Finsupp.mem_support_iff.mp ih))
  have hinj : Function.Injective (fun n : ℕ => T ^ n * γ) := by
    intro m n hmn
    have h2 : T ^ m = T ^ n := mul_right_cancel hmn
    have h3 : T ^ (m : ℤ) = T ^ (n : ℤ) := by rw [zpow_natCast, zpow_natCast]; exact h2
    have h4 : (m : ℤ) = (n : ℤ) := T_zpow_injective h3
    exact_mod_cast h4
  have hinf : (Set.range (fun n : ℕ => T ^ n * γ)).Infinite := Set.infinite_range_of_injective hinj
  refine hinf (((MonoidAlgebra.coeff u).support.finite_toSet).subset ?_)
  rintro _ ⟨n, rfl⟩
  exact hmem n

/-! ## 7. Lengths along the `⟨T⟩`-orbit of `y * z` -/

theorem toList_x_mul_of_NX {z : FP} (h : NX z) :
    (Monoid.CoprodI.Word.equiv (x * z)).toList
      = ⟨false, Lx.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  rw [show x = Monoid.CoprodI.of (M := Cyc) (i := false) Lx.2 from of_Lx.symm, equiv_mul]
  exact toList_smul_of_fstIdx_ne (i := false) Lx.2 _ Lx_ne_one h

theorem XF_x_mul_of_NX {z : FP} (h : NX z) : XF (x * z) := by
  rw [XF, Monoid.CoprodI.Word.fstIdx, toList_x_mul_of_NX h]
  simp

theorem toList_y_mul_of_XF {z : FP} (h : XF z) :
    (Monoid.CoprodI.Word.equiv (y * z)).toList
      = ⟨true, Ly.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  rw [equiv_mul]
  exact toList_smul_of_fstIdx_ne (i := true) Ly.2 _ Ly_ne_one h

theorem toList_y2_mul_of_XF {z : FP} (h : XF z) :
    (Monoid.CoprodI.Word.equiv (y2 * z)).toList
      = ⟨true, Ly2.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  rw [show y2 = Monoid.CoprodI.of (M := Cyc) (i := true) Ly2.2 from of_Ly2.symm, equiv_mul]
  exact toList_smul_of_fstIdx_ne (i := true) Ly2.2 _ Ly2_ne_one h

theorem elen_y_mul_of_XF {z : FP} (h : XF z) : elen (y * z) = elen z + 1 := by
  rw [elen, wlen, toList_y_mul_of_XF h]
  rfl

theorem elen_y2_mul_of_XF {z : FP} (h : XF z) : elen (y2 * z) = elen z + 1 := by
  rw [elen, wlen, toList_y2_mul_of_XF h]
  rfl

theorem NX_y_mul_of_XF {z : FP} (h : XF z) : NX (y * z) := by
  rw [NX, Monoid.CoprodI.Word.fstIdx, toList_y_mul_of_XF h]
  simp

theorem NX_y2_mul_of_XF {z : FP} (h : XF z) : NX (y2 * z) := by
  rw [NX, Monoid.CoprodI.Word.fstIdx, toList_y2_mul_of_XF h]
  simp

theorem NX_one_Ip : NX (1 : FP) := by
  rw [NX, equiv_one, fstIdx_empty]
  exact fun h => nomatch h

theorem elen_x_Ip : elen (x : FP) = 1 := by
  have h := elen_x_mul (γ := (1 : FP)) NX_one_Ip
  rw [mul_one, elen_one] at h
  simpa using h

theorem XF_x_Ip : XF (x : FP) := by
  have h := XF_x_mul_of_NX NX_one_Ip
  rwa [mul_one] at h

theorem toList_T_mul_y_mul_of_XF {z : FP} (h : XF z) :
    (Monoid.CoprodI.Word.equiv (T * (y * z))).toList
      = [⟨false, Lx.2⟩, ⟨true, Ly2.2⟩] ++ (Monoid.CoprodI.Word.equiv z).toList := by
  have h1 : T * (y * z) = x * (y2 * z) := by
    rw [T_eq, mul_assoc]
    congr 1
    rw [← mul_assoc, y2, pow_two]
  rw [h1, toList_x_mul_of_NX (NX_y2_mul_of_XF h), toList_y2_mul_of_XF h]
  rfl

theorem startsLx_T_mul_y_mul_of_XF {z : FP} (h : XF z) : StartsLx (T * (y * z)) := by
  rw [StartsLx, toList_T_mul_y_mul_of_XF h]
  rfl

theorem elen_T_mul_y_mul_of_XF {z : FP} (h : XF z) : elen (T * (y * z)) = elen z + 2 := by
  have h1 : T * (y * z) = x * (y2 * z) := by
    rw [T_eq, mul_assoc]
    congr 1
    rw [← mul_assoc, y2, pow_two]
  rw [h1, elen_x_mul (NX_y2_mul_of_XF h), elen_y2_mul_of_XF h]

theorem toList_Tinv_mul_y_mul_of_XF {z : FP} (h : XF z) :
    (Monoid.CoprodI.Word.equiv (T⁻¹ * (y * z))).toList
      = [⟨true, Ly2.2⟩, ⟨false, Lx.2⟩, ⟨true, Ly.2⟩]
        ++ (Monoid.CoprodI.Word.equiv z).toList := by
  have h1 : T⁻¹ * (y * z) = y2 * (x * (y * z)) := by rw [Tinv_eq, mul_assoc]
  have hx := toList_x_mul_of_NX (NX_y_mul_of_XF h)
  have h2 : (Monoid.CoprodI.Word.equiv (y2 * (x * (y * z)))).toList
      = ⟨true, Ly2.2⟩ :: (Monoid.CoprodI.Word.equiv (x * (y * z))).toList :=
    toList_y2_mul_of_XF (XF_x_mul_of_NX (NX_y_mul_of_XF h))
  rw [h1, h2, hx, toList_y_mul_of_XF h]
  rfl

theorem startsLy2_Tinv_mul_y_mul_of_XF {z : FP} (h : XF z) : StartsLy2 (T⁻¹ * (y * z)) := by
  rw [StartsLy2, toList_Tinv_mul_y_mul_of_XF h]
  rfl

theorem elen_Tinv_mul_y_mul_of_XF {z : FP} (h : XF z) :
    elen (T⁻¹ * (y * z)) = elen z + 3 := by
  have h1 : T⁻¹ * (y * z) = y2 * (x * (y * z)) := by rw [Tinv_eq, mul_assoc]
  rw [h1, show y2 * (x * (y * z)) = y2 * x * (y * z) from by rw [mul_assoc],
    elen_y2x_mul (NX_y_mul_of_XF h), elen_y_mul_of_XF h]

theorem split_T_pow_mul (m : ℕ) (hm : 1 ≤ m) (z : FP) :
    T ^ m * z = T ^ (m - 1) * (T * z) := by
  have h1 : m = (m - 1) + 1 := by omega
  calc T ^ m * z = T ^ ((m - 1) + 1) * z := by conv_lhs => rw [h1]
    _ = (T ^ (m - 1) * T) * z := by rw [pow_succ]
    _ = T ^ (m - 1) * (T * z) := by rw [mul_assoc]

theorem split_Tinv_pow_mul (m : ℕ) (hm : 1 ≤ m) (z : FP) :
    (T⁻¹) ^ m * z = (T⁻¹) ^ (m - 1) * (T⁻¹ * z) := by
  have h1 : m = (m - 1) + 1 := by omega
  calc (T⁻¹) ^ m * z = (T⁻¹) ^ ((m - 1) + 1) * z := by conv_lhs => rw [h1]
    _ = ((T⁻¹) ^ (m - 1) * T⁻¹) * z := by rw [pow_succ]
    _ = (T⁻¹) ^ (m - 1) * (T⁻¹ * z) := by rw [mul_assoc]

theorem T_pow_mul_startsLx (k : ℕ) {z : FP} (h : StartsLx z) : StartsLx (T ^ k * z) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', mul_assoc]; exact T_mul_startsLx ih

theorem elen_T_pow_mul_of_startsLx (k : ℕ) {z : FP} (h : StartsLx z) :
    elen (T ^ k * z) = elen z + 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, T_mul_elen (T_pow_mul_startsLx k h), ih]
    omega

theorem Tinv_pow_mul_startsLy2 (k : ℕ) {z : FP} (h : StartsLy2 z) :
    StartsLy2 ((T⁻¹) ^ k * z) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', mul_assoc]; exact Tinv_mul_startsLy2 ih

theorem elen_Tinv_pow_mul_of_startsLy2 (k : ℕ) {z : FP} (h : StartsLy2 z) :
    elen ((T⁻¹) ^ k * z) = elen z + 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, Tinv_mul_elen (Tinv_pow_mul_startsLy2 k h), ih]
    omega

/-- **The orbit of `y z` leaves the support.**  If `z` is `1` or starts with `x` and `n ≠ 0`,
then `Tⁿ (y z)` is strictly longer than `y z`. -/
theorem elen_T_zpow_mul_y_mul_of_XF {n : ℤ} (hn : n ≠ 0) {z : FP} (h : XF z) :
    elen z + 1 < elen (T ^ n * (y * z)) := by
  rcases lt_or_gt_of_ne hn.symm with hpos | hneg
  · set m := n.toNat with hm
    have hcast : ((m : ℤ)) = n := by
      rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ m := by omega
    have hT : T ^ n = T ^ m := by rw [← hcast, zpow_natCast]
    rw [hT, split_T_pow_mul m hm1 (y * z),
      elen_T_pow_mul_of_startsLx (m - 1) (startsLx_T_mul_y_mul_of_XF h),
      elen_T_mul_y_mul_of_XF h]
    omega
  · set m := (-n).toNat with hm
    have hcast : ((m : ℤ)) = -n := by
      rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ m := by omega
    have hT : T ^ n = (T⁻¹) ^ m := by
      have hnm : n = -((m : ℤ)) := by omega
      rw [hnm, zpow_neg, zpow_natCast, inv_pow]
    rw [hT, split_Tinv_pow_mul m hm1 (y * z),
      elen_Tinv_pow_mul_of_startsLy2 (m - 1) (startsLy2_Tinv_mul_y_mul_of_XF h),
      elen_Tinv_mul_y_mul_of_XF h]
    omega

/-- The three orbit-length bounds used in the three cases. -/
theorem elen_T_zpow_mul_ge {z : FP} (hz : XF z) {n : ℤ} (hn : n ≠ 0) :
    (4 + elen z ≤ elen (T ^ n * (y * x * y * z))) ∧
    (4 + elen z ≤ elen (T ^ n * (y * x * y2 * z))) ∧
    (3 ≤ elen (T ^ n * (y * x))) := by
  have h1 : elen (x * y * z) = elen z + 2 := elen_xy_mul_of_XF hz
  have h2 : elen (x * y2 * z) = elen z + 2 := elen_xy2_mul_of_XF hz
  have h3 : elen (x : FP) = 1 := elen_x_Ip
  have h4 : XF (x : FP) := XF_x_Ip
  have e1 : T ^ n * (y * x * y * z) = T ^ n * (y * (x * y * z)) := by
    rw [mul_assoc y x y, mul_assoc y (x * y) z]
  have e2 : T ^ n * (y * x * y2 * z) = T ^ n * (y * (x * y2 * z)) := by
    rw [mul_assoc y x y2, mul_assoc y (x * y2) z]
  have A := elen_T_zpow_mul_y_mul_of_XF hn (XF_xy_mul_of_XF hz)
  have B := elen_T_zpow_mul_y_mul_of_XF hn (XF_xy2_mul_of_XF hz)
  have C := elen_T_zpow_mul_y_mul_of_XF hn h4
  rw [h1] at A
  rw [h2] at B
  rw [h3] at C
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; omega
  · rw [e2]; omega
  · omega


/-! ## 8. The three cases of the coefficient analysis -/

theorem not_XF_y_mul_Ip {z : FP} (h : XF z) : ¬ XF (y * z) := by
  rw [XF, Monoid.CoprodI.Word.fstIdx, toList_y_mul_of_XF h]
  exact fun hc => nomatch hc

theorem not_XF_y2_mul_Ip {z : FP} (h : XF z) : ¬ XF (y2 * z) := by
  rw [XF, Monoid.CoprodI.Word.fstIdx, toList_y2_mul_of_XF h]
  exact fun hc => nomatch hc

theorem coeff_of_self (g : FP) : MonoidAlgebra.coeff ((MonoidAlgebra.of ℂ FP) g) g = 1 := by
  rw [show MonoidAlgebra.of ℂ FP g = MonoidAlgebra.single g (1:ℂ) from rfl,
    MonoidAlgebra.coeff_single_apply]
  simp

/-- The scalar part of `q * single 1 c`. -/
theorem q_mul_single_one (c : ℂ) :
    (q : RR) * MonoidAlgebra.single (1 : FP) c = c • q := by
  have hs : (MonoidAlgebra.single (1 : FP) c : RR) = c • (1 : RR) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hs, mul_smul_comm, mul_one]

/-- The coefficient of `q` vanishes on elements of length at least `3`. -/
theorem coeff_q_mul_single_eq_zero {c : ℂ} {z : FP} (hz : 3 ≤ elen z) :
    c * MonoidAlgebra.coeff (q : RR) z = 0 := by
  rw [coeff_q_of_three_le hz, mul_zero]

theorem coeff_qY_mul_eq_zero_of_long {r : RR} {N : ℕ}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ N) {z : FP} (hz : 3 + N < elen z) :
    MonoidAlgebra.coeff (qY * r) z = 0 := by
  have h1 : elen (y2 * x * y : FP) ≤ 3 := by decide
  have h2 : elen (y * x * y : FP) ≤ 3 := by decide
  have h3 : elen (x * y : FP) ≤ 3 := by decide
  have h4 : elen (1 : FP) ≤ 3 := by decide
  have h5 : elen (y2 : FP) ≤ 3 := by decide
  have h6 : elen (y : FP) ≤ 3 := by decide
  have hL : ∀ g : FP, elen g ≤ 3 → MonoidAlgebra.coeff r (g⁻¹ * z) = 0 := fun g hg =>
    coeff_inv_mul_eq_zero_of_long h hg hz
  have h4' : MonoidAlgebra.coeff r z = 0 := by
    simpa using coeff_inv_mul_eq_zero_of_long h h4 hz
  rw [coeff_qY_mul, hL _ h1, hL _ h2, hL _ h3, h4', hL _ h5, hL _ h6]
  ring

theorem coeff_qY2_mul_eq_zero_of_long {r : RR} {N : ℕ}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ N) {z : FP} (hz : 3 + N < elen z) :
    MonoidAlgebra.coeff (qY2 * r) z = 0 := by
  have h1 : elen (y2 * x * y2 : FP) ≤ 3 := by decide
  have h2 : elen (y * x * y2 : FP) ≤ 3 := by decide
  have h3 : elen (x * y2 : FP) ≤ 3 := by decide
  have h4 : elen (1 : FP) ≤ 3 := by decide
  have h5 : elen (y2 : FP) ≤ 3 := by decide
  have h6 : elen (y : FP) ≤ 3 := by decide
  have hL : ∀ g : FP, elen g ≤ 3 → MonoidAlgebra.coeff r (g⁻¹ * z) = 0 := fun g hg =>
    coeff_inv_mul_eq_zero_of_long h hg hz
  have h4' : MonoidAlgebra.coeff r z = 0 := by
    simpa using coeff_inv_mul_eq_zero_of_long h h4 hz
  rw [coeff_qY2_mul, hL _ h1, hL _ h2, hL _ h3, hL _ h6, h4', hL _ h5]
  ring

/-! ### The core case: `v = c • q` -/

theorem coeff_q_yx : MonoidAlgebra.coeff (q : RR) (y * x) = -1 := by
  have e1 : (Y2 * X : RR) = MonoidAlgebra.of ℂ FP (y2*x) := by
    show MonoidAlgebra.of ℂ FP y2 * MonoidAlgebra.of ℂ FP x = _; rw [← map_mul]
  have e2 : (Y * X : RR) = MonoidAlgebra.of ℂ FP (y*x) := by
    show MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP x = _; rw [← map_mul]
  have e3 : (Y2 : RR) = MonoidAlgebra.of ℂ FP y2 := rfl
  have e4 : (Y : RR) = MonoidAlgebra.of ℂ FP y := rfl
  have e5 : (X : RR) = MonoidAlgebra.of ℂ FP x := rfl
  have e6 : (1 : RR) = MonoidAlgebra.of ℂ FP (1 : FP) := (map_one _).symm
  have expand : ((Y2 - Y + 1 : RR) * (X + 1)) = Y2*X + Y2 - Y*X - Y + X + 1 := by noncomm_ring
  show MonoidAlgebra.coeff (((Y2 - Y + 1) * (X + 1) : RR)) (y * x) = -1
  rw [expand, e1, e2, e3, e4, e5, e6]
  simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_add, Finsupp.sub_apply, Finsupp.add_apply]
  rw [coeff_of_eq_zero_of_ne (g := y2*x) (by decide), coeff_of_self (y*x),
    coeff_of_eq_zero_of_ne (g := y2) (by decide), coeff_of_eq_zero_of_ne (g := y) (by decide),
    coeff_of_eq_zero_of_ne (g := x) (by decide), coeff_of_eq_zero_of_ne (g := (1 : FP)) (by decide)]
  ring

theorem core_contra {u : RR} {c : ℂ} (hc : c ≠ 0)
    (hv : (TT - 1) * u = q * MonoidAlgebra.single (1 : FP) c) : False := by
  have hlong : ∀ z : FP, 3 ≤ elen z → MonoidAlgebra.coeff ((TT - 1) * u) z = 0 := by
    intro z hz
    rw [hv, q_mul_single_one, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      coeff_q_of_three_le hz, mul_zero]
  have h0 : MonoidAlgebra.coeff ((TT - 1) * u) (y * x) = -c := by
    rw [hv, q_mul_single_one, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      coeff_q_yx]
    ring
  refine orbit_corollary (u := u) (w := (TT - 1) * u) (γ := y * x) (c := -c)
    T_zpow_injective rfl h0 (neg_ne_zero.mpr hc) ?_
  intro n hn
  refine hlong _ ?_
  have hb := (elen_T_zpow_mul_ge XF_x_Ip hn).2.2
  omega

/-! ### Branch 2: the maximal length element sits in the `Y²`-slot -/

theorem branch2_contra {u : RR} {c : ℂ} {r1 r2 : RR} {γ : FP}
    (hγ : XF γ)
    (h1XF : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, XF δ)
    (h1len : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, elen δ ≤ elen γ)
    (h2XF : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, XF δ)
    (h2len : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, elen δ ≤ elen γ)
    (hγr2 : MonoidAlgebra.coeff r2 γ ≠ 0)
    (hv : (TT - 1) * u = q * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2)) : False := by
  have hδlen : elen (y * x * y2 * γ) = elen γ + 3 := by
    rw [show y * x * y2 * γ = y * (x * y2 * γ) from by noncomm_ring,
      elen_y_mul_of_XF (XF_xy2_mul_of_XF hγ), elen_xy2_mul_of_XF hγ]
  have hlong : ∀ z : FP, 3 + elen γ < elen z →
      MonoidAlgebra.coeff ((TT - 1) * u) z = 0 := by
    intro z hz
    rw [hv, coeff_q_mul_split, coeff_q_mul_single_eq_zero (by omega),
      coeff_qY_mul_eq_zero_of_long h1len (by omega),
      coeff_qY2_mul_eq_zero_of_long h2len (by omega)]
    ring
  have hcoe : MonoidAlgebra.coeff ((TT - 1) * u) (y * x * y2 * γ) = -MonoidAlgebra.coeff r2 γ := by
    rw [hv, coeff_q_mul_split, coeff_q_mul_single_eq_zero (by rw [hδlen]; omega)]
    have hA : MonoidAlgebra.coeff (qY * r1) (y * x * y2 * γ) = 0 := by
      rw [coeff_qY_mul]
      have b1 : MonoidAlgebra.coeff r1 ((y2*x*y)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc,
          show (y2*x*y)⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly2,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r1 ((y*x*y)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show (y*x*y)⁻¹ * (y * x * y2) = y from by decide]
        exact not_XF_y_mul_Ip hγ
      have b3 : MonoidAlgebra.coeff r1 ((x*y)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc,
          show (x*y)⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r1 (y * x * y2 * γ) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [show (y * x * y2 : FP) = toProd [Ly,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b5 : MonoidAlgebra.coeff r1 (y2⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r1 (y⁻¹ * (y * x * y2 * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y2) = x * y2 from by decide]
        exact coeff_eq_zero_of_len_supp h1len (by rw [elen_xy2_mul_of_XF hγ]; omega)
      rw [b1, b2, b3, b4, b5, b6]
      ring
    have hB : MonoidAlgebra.coeff (qY2 * r2) (y * x * y2 * γ) = -MonoidAlgebra.coeff r2 γ := by
      rw [coeff_qY2_mul]
      have b1 : MonoidAlgebra.coeff r2 ((y2*x*y2)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc,
          show (y2*x*y2)⁻¹ * (y * x * y2) = toProd [Ly,Lx,Ly2,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r2 ((y*x*y2)⁻¹ * (y * x * y2 * γ)) = MonoidAlgebra.coeff r2 γ := by
        rw [← mul_assoc, show (y*x*y2)⁻¹ * (y * x * y2) = 1 from by decide, one_mul]
      have b3 : MonoidAlgebra.coeff r2 ((x*y2)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc,
          show (x*y2)⁻¹ * (y * x * y2) = toProd [Ly,Lx,Ly,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r2 (y⁻¹ * (y * x * y2 * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y2) = x * y2 from by decide]
        exact coeff_eq_zero_of_len_supp h2len (by rw [elen_xy2_mul_of_XF hγ]; omega)
      have b5 : MonoidAlgebra.coeff r2 (y * x * y2 * γ) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [show (y * x * y2 : FP) = toProd [Ly,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r2 (y2⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly2] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      rw [b1, b2, b3, b4, b5, b6]
      ring
    rw [hA, hB]
    ring
  refine orbit_corollary (u := u) (w := (TT - 1) * u) (γ := y * x * y2 * γ)
    (c := -MonoidAlgebra.coeff r2 γ) T_zpow_injective rfl hcoe (neg_ne_zero.mpr hγr2) ?_
  intro n hn
  refine hlong _ ?_
  have hb := (elen_T_zpow_mul_ge hγ hn).2.1
  omega

/-! ### Branch 1: the maximal length element sits in the `Y`-slot -/

theorem branch1_contra {u : RR} {c : ℂ} {r1 r2 : RR} {γ : FP}
    (hγ : XF γ)
    (h1XF : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, XF δ)
    (h1len : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, elen δ ≤ elen γ)
    (h2XF : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, XF δ)
    (h2len : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, elen δ ≤ elen γ)
    (h2van : ∀ z : FP, elen γ ≤ elen z → MonoidAlgebra.coeff r2 z = 0)
    (hγr1 : MonoidAlgebra.coeff r1 γ ≠ 0)
    (hv : (TT - 1) * u = q * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2)) : False := by
  have hδlen : elen (y * x * y * γ) = elen γ + 3 := by
    rw [show y * x * y * γ = y * (x * y * γ) from by noncomm_ring,
      elen_y_mul_of_XF (XF_xy_mul_of_XF hγ), elen_xy_mul_of_XF hγ]
  have hlong : ∀ z : FP, 3 + elen γ < elen z →
      MonoidAlgebra.coeff ((TT - 1) * u) z = 0 := by
    intro z hz
    rw [hv, coeff_q_mul_split, coeff_q_mul_single_eq_zero (by omega),
      coeff_qY_mul_eq_zero_of_long h1len (by omega),
      coeff_qY2_mul_eq_zero_of_long h2len (by omega)]
    ring
  have hcoe : MonoidAlgebra.coeff ((TT - 1) * u) (y * x * y * γ) = -MonoidAlgebra.coeff r1 γ := by
    rw [hv, coeff_q_mul_split, coeff_q_mul_single_eq_zero (by rw [hδlen]; omega)]
    have hA : MonoidAlgebra.coeff (qY * r1) (y * x * y * γ) = -MonoidAlgebra.coeff r1 γ := by
      rw [coeff_qY_mul]
      have b1 : MonoidAlgebra.coeff r1 ((y2*x*y)⁻¹ * (y * x * y * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc,
          show (y2*x*y)⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly2,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r1 ((y*x*y)⁻¹ * (y * x * y * γ)) = MonoidAlgebra.coeff r1 γ := by
        rw [← mul_assoc, show (y*x*y)⁻¹ * (y * x * y) = 1 from by decide, one_mul]
      have b3 : MonoidAlgebra.coeff r1 ((x*y)⁻¹ * (y * x * y * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show (x*y)⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r1 (y * x * y * γ) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [show (y * x * y : FP) = toProd [Ly,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b5 : MonoidAlgebra.coeff r1 (y2⁻¹ * (y * x * y * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r1 (y⁻¹ * (y * x * y * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y) = x * y from by decide]
        exact coeff_eq_zero_of_len_supp h1len (by rw [elen_xy_mul_of_XF hγ]; omega)
      rw [b1, b2, b3, b4, b5, b6]
      ring
    have hB : MonoidAlgebra.coeff (qY2 * r2) (y * x * y * γ) = 0 := by
      rw [coeff_qY2_mul]
      have b1 : MonoidAlgebra.coeff r2 ((y2*x*y2)⁻¹ * (y * x * y * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc,
          show (y2*x*y2)⁻¹ * (y * x * y) = toProd [Ly,Lx,Ly2,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r2 ((y*x*y2)⁻¹ * (y * x * y * γ)) = 0 := by
        rw [← mul_assoc, show (y*x*y2)⁻¹ * (y * x * y) = y2 from by decide]
        exact coeff_eq_zero_of_not_XF_supp h2XF (not_XF_y2_mul_Ip hγ)
      have b3 : MonoidAlgebra.coeff r2 ((x*y2)⁻¹ * (y * x * y * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc, show (x*y2)⁻¹ * (y * x * y) = toProd [Ly,Lx,Ly,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r2 (y⁻¹ * (y * x * y * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y) = x * y from by decide]
        exact h2van _ (by rw [elen_xy_mul_of_XF hγ]; omega)
      have b5 : MonoidAlgebra.coeff r2 (y * x * y * γ) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [show (y * x * y : FP) = toProd [Ly,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r2 (y2⁻¹ * (y * x * y * γ)) = 0 := by
        refine coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly] from by decide]
        exact not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      rw [b1, b2, b3, b4, b5, b6]
      ring
    rw [hA, hB]
    ring
  refine orbit_corollary (u := u) (w := (TT - 1) * u) (γ := y * x * y * γ)
    (c := -MonoidAlgebra.coeff r1 γ) T_zpow_injective rfl hcoe (neg_ne_zero.mpr hγr1) ?_
  intro n hn
  refine hlong _ ?_
  have hb := (elen_T_zpow_mul_ge hγ hn).1
  omega


/-! ## 9. Maximal support length and the final assembly -/

/-- The maximal length of a group element in the support of `r`. -/
def rlen (r : RR) : ℕ := (MonoidAlgebra.coeff r).support.sup (fun γ => elen γ)

theorem rlen_le_of_mem {r : RR} {δ : FP}
    (h : δ ∈ (MonoidAlgebra.coeff r).support) : elen δ ≤ rlen r :=
  Finset.le_sup h

theorem exists_rlen {r : RR} (h : r ≠ 0) :
    ∃ δ ∈ (MonoidAlgebra.coeff r).support, elen δ = rlen r := by
  have hne : (MonoidAlgebra.coeff r).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (fun hc => h (MonoidAlgebra.coeff_eq_zero.mp hc))
  obtain ⟨δ, hδ, hsup⟩ := Finset.exists_mem_eq_sup _ hne (fun γ => elen γ)
  exact ⟨δ, hδ, hsup.symm⟩

theorem rlen_zero : rlen (0 : RR) = 0 := by simp [rlen]

end IpDirect

end

/-- **The direct sum `(X + 1)·RR ∩ (T - 1)²·RR = 0`.**  If `(T - 1)² u = (X + 1) w` then
`u = 0`. -/
theorem IdealIpDirect {u w : Work.FreeProduct.RR}
    (h : (Work.FreeProduct.TT - 1) ^ 2 * u = (Work.FreeProduct.X + 1) * w) : u = 0 := by
  set v : RR := (TT - 1) * u with hv
  have hv2 : (TT - 1) * v = (X + 1) * w := by
    rw [hv, ← mul_assoc, ← pow_two]; exact h
  obtain ⟨r, hr⟩ := IpDirect.mem_qR_of_sub_one_mem hv2
  obtain ⟨c, r1, r2, t, hdec, h1XF, h2XF⟩ := IpDirect.exists_canon_MUp r
  have hqX : ((Y2 - Y + 1 : RR) * (X + 1)) * (X - 1) = 0 := IpDirect.q_mul_X_sub_one
  have hzero : ((Y2 - Y + 1 : RR) * (X + 1)) * ((X - 1) * t) = 0 := by
    rw [← mul_assoc, hqX, zero_mul]
  have hv' : v = ((Y2 - Y + 1 : RR) * (X + 1))
      * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2) := by
    rw [hr, hdec, mul_add, hzero, add_zero]
  by_cases h12 : r1 = 0 ∧ r2 = 0
  · obtain ⟨hr1, hr2⟩ := h12
    rw [hr1, hr2, mul_zero, mul_zero, add_zero, add_zero] at hv'
    by_cases hc : c = 0
    · rw [hc, MonoidAlgebra.single_zero, mul_zero] at hv'
      exact IpDirect.TT_sub_one_eq_zero (by rw [← hv]; exact hv')
    · exact absurd (IpDirect.core_contra (u := u) (c := c) hc (by rw [← hv]; exact hv'))
        (by simp)
  · by_cases hb : r2 ≠ 0 ∧ IpDirect.rlen r1 ≤ IpDirect.rlen r2
    · obtain ⟨hr2ne, hle⟩ := hb
      obtain ⟨γ, hγmem, hγlen⟩ := IpDirect.exists_rlen hr2ne
      exact (IpDirect.branch2_contra (u := u) (c := c) (r1 := r1) (r2 := r2) (γ := γ)
        (h2XF γ hγmem) (fun δ hδ => h1XF δ hδ)
        (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
        (fun δ hδ => h2XF δ hδ)
        (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
        (Finsupp.mem_support_iff.mp hγmem)
        (by rw [← hv]; exact hv')).elim
    · by_cases hr2z : r2 = 0
      · have hr1ne : r1 ≠ 0 := by
          rintro rfl
          exact h12 ⟨rfl, hr2z⟩
        obtain ⟨γ, hγmem, hγlen⟩ := IpDirect.exists_rlen hr1ne
        exact (IpDirect.branch1_contra (u := u) (c := c) (r1 := r1) (r2 := r2) (γ := γ)
          (h1XF γ hγmem)
          (fun δ hδ => h1XF δ hδ)
          (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
          (fun δ hδ => by rw [hr2z] at hδ; simp at hδ)
          (fun δ hδ => by rw [hr2z] at hδ; simp at hδ)
          (fun z _ => by rw [hr2z]; simp)
          (Finsupp.mem_support_iff.mp hγmem)
          (by rw [← hv]; exact hv')).elim
      · have hlt : IpDirect.rlen r2 < IpDirect.rlen r1 := by
          rcases lt_or_ge (IpDirect.rlen r2) (IpDirect.rlen r1) with hh | hh
          · exact hh
          · exact absurd ⟨hr2z, hh⟩ hb
        have hr1ne : r1 ≠ 0 := by
          rintro rfl
          rw [IpDirect.rlen_zero] at hlt
          omega
        obtain ⟨γ, hγmem, hγlen⟩ := IpDirect.exists_rlen hr1ne
        exact (IpDirect.branch1_contra (u := u) (c := c) (r1 := r1) (r2 := r2) (γ := γ)
          (h1XF γ hγmem)
          (fun δ hδ => h1XF δ hδ)
          (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
          (fun δ hδ => h2XF δ hδ)
          (fun δ hδ => by
            have h1 := IpDirect.rlen_le_of_mem hδ
            rw [← hγlen] at hlt
            omega)
          (fun z hz => by
            by_contra hc
            have h1 := IpDirect.rlen_le_of_mem (Finsupp.mem_support_iff.mpr hc)
            rw [hγlen] at hz
            omega)
          (Finsupp.mem_support_iff.mp hγmem)
          (by rw [← hv]; exact hv')).elim

end Work.FreeProduct
