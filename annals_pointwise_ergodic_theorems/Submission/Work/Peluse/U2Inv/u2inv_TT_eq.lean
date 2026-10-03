import Mathlib
import Submission.Work.Peluse.U2Inv.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `U²`-inverse Fourier identity for the twisted sum `TT`

The twisted `U²` quantity `TT L k₁ k₂ F` is the `ℓ⁴`-norm of the discrete Fourier transform of
`F`, twisted by the two shifts `k₁, k₂`:

`TT L k₁ k₂ F = (4L+1)^{-4} ∑_ξ 𝓕F (ξ+k₁+k₂) · conj (𝓕F (ξ+k₁)) · conj (𝓕F (ξ+k₂)) · 𝓕F ξ`.

The proof is an explicit finite Fourier computation.  Writing `Δ_{a,b} F (x)` for the second
difference, the `x`-sum and the two shift sums, after expanding the four factors by Fourier
inversion, are evaluations of the orthogonality relation `∑_c χ (c * t) = #G · [t = 0]`; this is
`ttCharCollapse`.  The factorisation trick `ttFactor` reduces the number of expansions by one:
the `(x,b)`-sum of the difference is a product of two twisted autocorrelations.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-! ## Character arithmetic -/

/-- `conj (χ t) = χ (-t)` for the standard additive character. -/
lemma ttStarChar {N : ℕ} [NeZero N] (t : ZMod N) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [AddChar.map_neg_eq_inv]
  have h : ‖ZMod.stdAddChar t‖ = 1 := by
    rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  exact (Complex.inv_eq_conj h).symm

/-- Product of the three characters occurring in the expansion of the difference operator. -/
lemma ttCharProd {N : ℕ} [NeZero N] (x k ξ₁ ξ₂ : ZMod N) :
    ZMod.stdAddChar (x*k) * ZMod.stdAddChar (-(x*ξ₁)) * ZMod.stdAddChar (x*ξ₂)
      = ZMod.stdAddChar (x*(k - ξ₁ + ξ₂)) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Orthogonality of the additive characters of `ZMod N`. -/
lemma ttSumCharMul {N : ℕ} [NeZero N] (t : ZMod N) :
    ∑ c : ZMod N, ZMod.stdAddChar (c * t) = if t = 0 then (N:ℂ) else 0 := by
  rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar N)]
  simp [ZMod.card]

/-- The `U²` "collapse": a sum of two Fourier expansions against a character collapses to a
single sum over the frequency variable. -/
lemma ttCharCollapse {N : ℕ} [NeZero N] (k : ZMod N) (c₁ c₂ : ZMod N → ℂ) :
    (∑ x : ZMod N, ZMod.stdAddChar (x*k) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (-(x*ξ)) * c₁ ξ) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (x*ξ) * c₂ ξ))
      = (N:ℂ) * ∑ ξ : ZMod N, c₁ (ξ+k) * c₂ ξ := by
  have h1 : ∀ x : ZMod N,
      ZMod.stdAddChar (x*k) * (∑ ξ : ZMod N, ZMod.stdAddChar (-(x*ξ)) * c₁ ξ) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (x*ξ) * c₂ ξ)
      = ∑ ξ₁ : ZMod N, ∑ ξ₂ : ZMod N,
          ZMod.stdAddChar (x*(k - ξ₁ + ξ₂)) * (c₁ ξ₁ * c₂ ξ₂) := by
    intro x
    rw [mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ₁ _ => Finset.sum_congr rfl (fun ξ₂ _ => ?_))
    rw [show ZMod.stdAddChar (x * k) *
        (ZMod.stdAddChar (-(x * ξ₁)) * c₁ ξ₁ * (ZMod.stdAddChar (x * ξ₂) * c₂ ξ₂))
        = ZMod.stdAddChar (x*(k-ξ₁+ξ₂)) * (c₁ ξ₁ * c₂ ξ₂) from by
          rw [← ttCharProd x k ξ₁ ξ₂]; ring]
  have hpred : ∀ ξ₁ ξ₂ : ZMod N, (k - ξ₁ + ξ₂ = 0) ↔ (ξ₁ = ξ₂ + k) := fun ξ₁ ξ₂ ↦ by
    rw [show k - ξ₁ + ξ₂ = ξ₂ + k - ξ₁ by ring, sub_eq_zero]
    exact eq_comm
  calc (∑ x : ZMod N, ZMod.stdAddChar (x*k) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (-(x*ξ)) * c₁ ξ) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (x*ξ) * c₂ ξ))
      = ∑ x : ZMod N, ∑ ξ₁ : ZMod N, ∑ ξ₂ : ZMod N,
          ZMod.stdAddChar (x*(k - ξ₁ + ξ₂)) * (c₁ ξ₁ * c₂ ξ₂) :=
        Finset.sum_congr rfl (fun x _ => h1 x)
    _ = ∑ ξ₁ : ZMod N, ∑ ξ₂ : ZMod N, ∑ x : ZMod N,
          ZMod.stdAddChar (x*(k - ξ₁ + ξ₂)) * (c₁ ξ₁ * c₂ ξ₂) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun ξ₁ _ => Finset.sum_comm)
    _ = ∑ ξ₁ : ZMod N, ∑ ξ₂ : ZMod N,
          (if k - ξ₁ + ξ₂ = 0 then (N:ℂ) else 0) * (c₁ ξ₁ * c₂ ξ₂) := by
        refine Finset.sum_congr rfl (fun ξ₁ _ => Finset.sum_congr rfl (fun ξ₂ _ => ?_))
        rw [← Finset.sum_mul, ttSumCharMul]
    _ = (N:ℂ) * ∑ ξ : ZMod N, c₁ (ξ+k) * c₂ ξ := by
        simp only [hpred]
        rw [Finset.mul_sum, Finset.sum_comm]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `ttCharCollapse` with the character on the right rather than the left. -/
lemma ttCharCollapseEnd {N : ℕ} [NeZero N] (k : ZMod N) (c₁ c₂ : ZMod N → ℂ) :
    (∑ x : ZMod N,
        (∑ ξ : ZMod N, ZMod.stdAddChar (-(x*ξ)) * c₁ ξ) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (x*ξ) * c₂ ξ) * ZMod.stdAddChar (x*k))
      = (N:ℂ) * ∑ ξ : ZMod N, c₁ (ξ+k) * c₂ ξ := by
  rw [show (∑ x : ZMod N, (∑ ξ : ZMod N, ZMod.stdAddChar (-(x*ξ)) * c₁ ξ) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (x*ξ) * c₂ ξ) * ZMod.stdAddChar (x*k))
      = (∑ x : ZMod N, ZMod.stdAddChar (x*k) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (-(x*ξ)) * c₁ ξ) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (x*ξ) * c₂ ξ)) from
      Finset.sum_congr rfl (fun x _ => by ring)]
  exact ttCharCollapse k c₁ c₂

/-- `N⁻² · (N · X) = N⁻¹ · X`. -/
lemma ttInvSqMul {N : ℕ} [NeZero N] (X : ℂ) :
    (N:ℂ)⁻¹ * (N:ℂ)⁻¹ * ((N:ℂ) * X) = (N:ℂ)⁻¹ * X := by
  rw [show (N:ℂ)⁻¹ * (N:ℂ)⁻¹ * ((N:ℂ) * X) = ((N:ℂ)⁻¹ * ((N:ℂ)⁻¹ * (N:ℂ))) * X by ring,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), mul_one]

/-! ## Fourier inversion -/

/-- Fourier inversion on `ZMod N`. -/
lemma ttDftInv {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (y : ZMod N) :
    F y = ((N:ℂ))⁻¹ * ∑ ξ : ZMod N, ZMod.stdAddChar (y * ξ) * ZMod.dft F ξ := by
  have h := ZMod.invDFT_apply (ZMod.dft F) y
  rw [show ZMod.dft.symm (ZMod.dft F) = F from LinearEquiv.symm_apply_apply _ _] at h
  rw [h]
  simp only [smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl (fun ξ _ => by rw [mul_comm ξ y])

/-- Fourier inversion for the conjugate. -/
lemma ttStarDftInv {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (y : ZMod N) :
    star (F y) = ((N:ℂ))⁻¹ *
      ∑ ξ : ZMod N, ZMod.stdAddChar (-(y * ξ)) * star (ZMod.dft F ξ) := by
  rw [ttDftInv F y]
  rw [star_mul, star_sum, star_inv₀, star_natCast, mul_comm]
  congr 1
  exact Finset.sum_congr rfl (fun ξ _ => by rw [star_mul, ttStarChar, mul_comm])

/-! ## The shifted autocorrelation `Q` and its Fourier expansion -/

/-- The twisted autocorrelation `Q_a = ∑_y conj (F y) · F (y+a) · χ (y k₂)`. -/
noncomputable def ttQ {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (k₂ : ZMod N) (a : ZMod N) : ℂ :=
  ∑ y : ZMod N, star (F y) * F (y + a) * ZMod.stdAddChar (y * k₂)

/-- Fourier expansion of `ttQ`. -/
lemma ttQ_eq {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (k₂ a : ZMod N) :
    ttQ F k₂ a = (N:ℂ)⁻¹ * ∑ ξ : ZMod N,
      ZMod.stdAddChar (a*ξ) * (star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ) := by
  have hFc : ∀ y : ZMod N, star (F y) = (N:ℂ)⁻¹ *
      ∑ ξ : ZMod N, ZMod.stdAddChar (-(y * ξ)) * star (ZMod.dft F ξ) :=
    fun y => ttStarDftInv F y
  have hFshift : ∀ y : ZMod N, F (y+a) = (N:ℂ)⁻¹ *
      ∑ ξ : ZMod N, ZMod.stdAddChar (y*ξ) * (ZMod.stdAddChar (a*ξ) * ZMod.dft F ξ) := by
    intro y
    rw [ttDftInv F (y+a)]
    congr 1
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [show (y+a)*ξ = y*ξ + a*ξ by ring, AddChar.map_add_eq_mul]
    ring
  have h1 : ttQ F k₂ a = (N:ℂ)⁻¹ * (N:ℂ)⁻¹ * ∑ y : ZMod N,
      ZMod.stdAddChar (y*k₂) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (-(y*ξ)) * star (ZMod.dft F ξ)) *
        (∑ ξ : ZMod N, ZMod.stdAddChar (y*ξ) * (ZMod.stdAddChar (a*ξ) * ZMod.dft F ξ)) := by
    rw [ttQ]
    have hpt : ∀ y : ZMod N, star (F y) * F (y+a) * ZMod.stdAddChar (y*k₂)
        = (N:ℂ)⁻¹ * (∑ ξ : ZMod N, ZMod.stdAddChar (-(y*ξ)) * star (ZMod.dft F ξ)) *
          (N:ℂ)⁻¹ * (∑ ξ : ZMod N, ZMod.stdAddChar (y*ξ) * (ZMod.stdAddChar (a*ξ) * ZMod.dft F ξ)) *
          ZMod.stdAddChar (y*k₂) := by
      intro y
      rw [hFc y, hFshift y]
      ring
    rw [Finset.sum_congr rfl (fun y _ => hpt y)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  rw [h1, ttCharCollapse k₂ (fun ξ => star (ZMod.dft F ξ))
        (fun ξ => ZMod.stdAddChar (a*ξ) * ZMod.dft F ξ)]
  rw [ttInvSqMul]
  have hsum : (∑ ξ : ZMod N, star (ZMod.dft F (ξ + k₂)) * (ZMod.stdAddChar (a*ξ) * ZMod.dft F ξ))
      = ∑ ξ : ZMod N, ZMod.stdAddChar (a*ξ) * (star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ) := by
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    ring
  rw [hsum]

/-- Reindexing a sum by the translation `b ↦ b - x`. -/
lemma ttSumShift {N : ℕ} [NeZero N] (x : ZMod N) (g : ZMod N → ℂ) :
    (∑ b : ZMod N, g b) = ∑ y : ZMod N, g (y + -x) := by
  rw [← Equiv.sum_comp (Equiv.addRight (-x)) g]
  simp [Equiv.addRight]

/-- The `(x,b)`-sum of the second difference factors as a product of two twisted
autocorrelations. -/
lemma ttFactor {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (k₂ a : ZMod N) :
    (∑ x : ZMod N, ∑ b : ZMod N, DeltaG a b F x * ZMod.stdAddChar (b*k₂))
      = star (ttQ F k₂ a) * ttQ F k₂ a := by
  have hsub : ∀ x : ZMod N,
      (∑ b : ZMod N, DeltaG a b F x * ZMod.stdAddChar (b*k₂))
      = ∑ y : ZMod N,
          star (F (x+a)) * star (F y) * F (y+a) * F x * ZMod.stdAddChar ((y + -x)*k₂) := by
    intro x
    rw [ttSumShift x (fun b : ZMod N => DeltaG a b F x * ZMod.stdAddChar (b*k₂))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [DeltaG]
    rw [show x + (y + -x) = y by ring, show x + a + (y + -x) = y + a by ring]
  have hfac : ∀ x : ZMod N,
      (∑ y : ZMod N,
          star (F (x+a)) * star (F y) * F (y+a) * F x * ZMod.stdAddChar ((y + -x)*k₂))
      = (star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂)) * ttQ F k₂ a := by
    intro x
    have hχ : ∀ y : ZMod N, ZMod.stdAddChar ((y + -x)*k₂)
        = ZMod.stdAddChar (y*k₂) * ZMod.stdAddChar ((-x)*k₂) := by
      intro y
      rw [show (y + -x)*k₂ = y*k₂ + (-x)*k₂ by ring, AddChar.map_add_eq_mul]
    calc (∑ y : ZMod N,
            star (F (x+a)) * star (F y) * F (y+a) * F x * ZMod.stdAddChar ((y + -x)*k₂))
        = ∑ y : ZMod N, (star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂)) *
              (star (F y) * F (y+a) * ZMod.stdAddChar (y*k₂)) := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [hχ y]; ring
      _ = (star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂)) *
            (∑ y : ZMod N, star (F y) * F (y+a) * ZMod.stdAddChar (y*k₂)) := by
            rw [Finset.mul_sum]
      _ = (star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂)) * ttQ F k₂ a := rfl
  have hlast : (∑ x : ZMod N, star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂))
      = star (ttQ F k₂ a) := by
    rw [show ttQ F k₂ a = (∑ y : ZMod N, star (F y) * F (y+a) * ZMod.stdAddChar (y*k₂))
          from rfl, star_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_mul, star_mul, star_star, ttStarChar]
    rw [show -(y*k₂) = (-y)*k₂ by ring]
    ring
  calc (∑ x : ZMod N, ∑ b : ZMod N, DeltaG a b F x * ZMod.stdAddChar (b*k₂))
      = ∑ x : ZMod N, ∑ y : ZMod N,
          star (F (x+a)) * star (F y) * F (y+a) * F x * ZMod.stdAddChar ((y + -x)*k₂) :=
        Finset.sum_congr rfl (fun x _ => hsub x)
    _ = ∑ x : ZMod N, (star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂)) * ttQ F k₂ a :=
        Finset.sum_congr rfl (fun x _ => hfac x)
    _ = (∑ x : ZMod N, star (F (x+a)) * F x * ZMod.stdAddChar ((-x)*k₂)) * ttQ F k₂ a := by
        rw [Finset.sum_mul]
    _ = star (ttQ F k₂ a) * ttQ F k₂ a := by rw [hlast]

theorem u2inv_TT_eq (L : ℕ) (k₁ k₂ : ZMod (Work.Peluse.U2Inv.Gmod L))
    (F : ZMod (Work.Peluse.U2Inv.Gmod L) → ℂ) :
    Work.Peluse.U2Inv.TT L k₁ k₂ F = (((Work.Peluse.U2Inv.Gmod L : ℂ)) ^ 4)⁻¹ *
      ∑ ξ : ZMod (Work.Peluse.U2Inv.Gmod L),
        ZMod.dft F (ξ + k₁ + k₂) * star (ZMod.dft F (ξ + k₁)) *
          star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ := by
  have hmain : (∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
        DeltaG a b F x * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂))
      = ((Gmod L : ℂ))⁻¹ * ∑ ξ : ZMod (Gmod L),
          star (ZMod.dft F (ξ + k₁)) * ZMod.dft F (ξ + k₁ + k₂) *
            star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ := by
    have h1 : (∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
          DeltaG a b F x * ZMod.stdAddChar (a*k₁) * ZMod.stdAddChar (b*k₂))
        = ∑ a : ZMod (Gmod L), ZMod.stdAddChar (a*k₁) * (star (ttQ F k₂ a) * ttQ F k₂ a) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have haux : (∑ x : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
            (DeltaG a b F x * ZMod.stdAddChar (a*k₁)) * ZMod.stdAddChar (b*k₂))
          = ZMod.stdAddChar (a*k₁) *
            (∑ x : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
              DeltaG a b F x * ZMod.stdAddChar (b*k₂)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      rw [haux, ttFactor F k₂ a]
    rw [h1]
    have hQ1 : ∀ a : ZMod (Gmod L), ttQ F k₂ a = ((Gmod L : ℂ))⁻¹ *
        ∑ ξ : ZMod (Gmod L),
          ZMod.stdAddChar (a*ξ) * (star (ZMod.dft F (ξ+k₂)) * ZMod.dft F ξ) :=
      fun a => ttQ_eq F k₂ a
    have hQ2 : ∀ a : ZMod (Gmod L), star (ttQ F k₂ a) = ((Gmod L : ℂ))⁻¹ *
        ∑ ξ : ZMod (Gmod L),
          ZMod.stdAddChar (-(a*ξ)) * (ZMod.dft F (ξ+k₂) * star (ZMod.dft F ξ)) := by
      intro a
      rw [ttQ_eq F k₂ a]
      rw [star_mul, star_sum, star_inv₀, star_natCast, mul_comm]
      congr 1
      exact Finset.sum_congr rfl (fun ξ _ => by
        rw [star_mul, star_mul, star_star, ttStarChar]; ring)
    have key : ∀ a : ZMod (Gmod L),
        ZMod.stdAddChar (a*k₁) * (star (ttQ F k₂ a) * ttQ F k₂ a)
        = (((Gmod L : ℂ))⁻¹ * ((Gmod L : ℂ))⁻¹) *
          (ZMod.stdAddChar (a*k₁) *
            (∑ ξ : ZMod (Gmod L),
              ZMod.stdAddChar (-(a*ξ)) * (ZMod.dft F (ξ+k₂) * star (ZMod.dft F ξ))) *
            (∑ ξ : ZMod (Gmod L),
              ZMod.stdAddChar (a*ξ) * (star (ZMod.dft F (ξ+k₂)) * ZMod.dft F ξ))) := by
      intro a
      rw [hQ2 a, hQ1 a]
      ring
    have hstep : (∑ a : ZMod (Gmod L), ZMod.stdAddChar (a*k₁) * (star (ttQ F k₂ a) * ttQ F k₂ a))
        = (((Gmod L : ℂ))⁻¹ * ((Gmod L : ℂ))⁻¹) *
          ∑ a : ZMod (Gmod L), ZMod.stdAddChar (a*k₁) *
            (∑ ξ : ZMod (Gmod L),
              ZMod.stdAddChar (-(a*ξ)) * (ZMod.dft F (ξ+k₂) * star (ZMod.dft F ξ))) *
            (∑ ξ : ZMod (Gmod L),
              ZMod.stdAddChar (a*ξ) * (star (ZMod.dft F (ξ+k₂)) * ZMod.dft F ξ)) := by
      rw [Finset.sum_congr rfl (fun a _ => key a)]
      rw [Finset.mul_sum]
    rw [hstep]
    rw [ttCharCollapse k₁ (fun ξ => ZMod.dft F (ξ+k₂) * star (ZMod.dft F ξ))
          (fun ξ => star (ZMod.dft F (ξ+k₂)) * ZMod.dft F ξ)]
    rw [ttInvSqMul]
    have hsum : (∑ ξ : ZMod (Gmod L),
          (fun η => ZMod.dft F (η+k₂) * star (ZMod.dft F η)) (ξ+k₁) *
            (star (ZMod.dft F (ξ+k₂)) * ZMod.dft F ξ))
        = ∑ ξ : ZMod (Gmod L),
          star (ZMod.dft F (ξ + k₁)) * ZMod.dft F (ξ + k₁ + k₂) *
            star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ := by
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      ring
    rw [hsum]
  rw [TT, hmain]
  have hT : (∑ ξ : ZMod (Gmod L), star (ZMod.dft F (ξ + k₁)) * ZMod.dft F (ξ + k₁ + k₂) *
        star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ)
      = ∑ ξ : ZMod (Gmod L), ZMod.dft F (ξ + k₁ + k₂) * star (ZMod.dft F (ξ + k₁)) *
        star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ := by
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    ring
  rw [hT, ← mul_assoc, ← mul_inv,
    show (Gmod L : ℂ)^3 * (Gmod L : ℂ) = (Gmod L : ℂ)^4 by ring]

end

end Work.Peluse.U2Inv
