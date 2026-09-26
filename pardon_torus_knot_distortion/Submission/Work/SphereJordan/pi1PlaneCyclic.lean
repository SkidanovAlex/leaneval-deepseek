import Mathlib

/-!
# `π₁(ℂ ∖ {0})` is cyclic, via the universal covering `exp`

The master lemma is `homotopic_of_lift_endpoints_eq`: two loops in `ℂ ∖ {0}` based at the same
point are homotopic as soon as their lifts through `Complex.exp : ℂ → ℂ ∖ {0}` (started at the
same logarithm of the base point) have the same endpoint.  Reason: the lifts are paths in the
simply connected (indeed contractible) set `ℂ` with equal endpoints, hence homotopic rel endpoints
there; pushing the homotopy forward along `exp` (a covering map, hence locally injective) gives a
homotopy of the loops.
-/

namespace Work.SphereJordan

open Set

noncomputable section

/-- The punctured plane, as a type. -/
abbrev Cs : Type := ↥(({0} : Set ℂ)ᶜ)

/-- The covering map `ℂ → ℂ ∖ {0}`, `z ↦ exp z`. -/
def expP : C(ℂ, Cs) where
  toFun z := ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  continuous_toFun := Continuous.subtype_mk Complex.continuous_exp _

@[simp] theorem expP_apply (z : ℂ) : ((expP z : ℂ)) = Complex.exp z := rfl

theorem isCoveringMap_expP : IsCoveringMap expP := Complex.isCoveringMap_exp

/-- The lift of a loop `γ` based at `expP ζ`, started at `ζ`, as a path in `ℂ`. -/
def liftLoop {ζ : ℂ} (γ : Path (expP ζ) (expP ζ)) :
    Path ζ (isCoveringMap_expP.liftPath γ ζ (Path.source γ) 1) where
  toContinuousMap := isCoveringMap_expP.liftPath γ ζ (Path.source γ)
  source' := isCoveringMap_expP.liftPath_zero γ ζ (Path.source γ)
  target' := rfl

@[simp] theorem liftLoop_apply {ζ : ℂ} (γ : Path (expP ζ) (expP ζ)) (t : unitInterval) :
    liftLoop γ t = isCoveringMap_expP.liftPath γ ζ (Path.source γ) t := rfl

theorem expP_liftLoop {ζ : ℂ} (γ : Path (expP ζ) (expP ζ)) (t : unitInterval) :
    expP (liftLoop γ t) = γ t :=
  congrFun (IsCoveringMap.liftPath_lifts isCoveringMap_expP γ ζ (Path.source γ)) t

/-- **Master lemma.**  Two loops in `ℂ ∖ {0}` based at `expP ζ` whose lifts from `ζ` end at the same
point are homotopic. -/
theorem homotopic_of_lift_endpoints_eq {ζ : ℂ} {γ₁ γ₂ : Path (expP ζ) (expP ζ)}
    (heq : (isCoveringMap_expP.liftPath γ₁ ζ (Path.source γ₁)) 1 =
        (isCoveringMap_expP.liftPath γ₂ ζ (Path.source γ₂)) 1) :
    γ₁.Homotopic γ₂ := by
  haveI : SimplyConnectedSpace ℂ := inferInstance
  set L₁ := liftLoop γ₁ with hL₁def
  set L₂ := liftLoop γ₂ with hL₂def
  have hL₁ : L₁ 1 = (isCoveringMap_expP.liftPath γ₁ ζ (Path.source γ₁)) 1 := rfl
  have hL₂ : L₂ 1 = (isCoveringMap_expP.liftPath γ₂ ζ (Path.source γ₂)) 1 := rfl
  have heq' : L₁ 1 = L₂ 1 := by rw [hL₁, hL₂]; exact heq
  -- the two lifts are homotopic because `ℂ` is simply connected
  have hhom : L₁.Homotopic (L₂.cast rfl heq') := SimplyConnectedSpace.paths_homotopic L₁ _
  have hmap : (L₁.map expP.continuous).Homotopic
      ((L₂.cast rfl heq').map expP.continuous) := hhom.map expP
  -- the endpoint equality needed to cast the loops
  have h₁ : expP (L₁ 1) = expP ζ := by
    rw [hL₁]
    exact (expP_liftLoop γ₁ 1).trans (Path.target γ₁)
  -- identify the images with the (cast) loops
  have e₁ : (L₁.map expP.continuous) = γ₁.cast rfl h₁ := by
    apply Path.ext
    funext t
    exact expP_liftLoop γ₁ t
  have e₂ : ((L₂.cast rfl heq').map expP.continuous) = γ₂.cast rfl h₁ := by
    apply Path.ext
    funext t
    exact expP_liftLoop γ₂ t
  rw [e₁, e₂] at hmap
  -- remove the casts again
  have hcast := Path.Homotopic.pathCast hmap rfl h₁.symm
  exact hcast

/-! ## The straight lift and the power loops -/

/-- The straight path from `ζ` to `ζ + n·(2πi)`. -/
def straightLift (ζ : ℂ) (n : ℤ) : Path ζ (ζ + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) where
  toContinuousMap :=
    ⟨fun t : unitInterval => ζ + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℝ),
      by fun_prop⟩
  source' := by simp
  target' := by simp

@[simp] theorem straightLift_apply (ζ : ℂ) (n : ℤ) (t : unitInterval) :
    straightLift ζ n t = ζ + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℝ) := rfl

/-- The loop `t ↦ x · exp (n·2πi·t)`. -/
def powerLoop (x : Cs) (n : ℤ) : Path x x where
  toContinuousMap :=
    ⟨fun t : unitInterval =>
      ⟨(x : ℂ) * Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℝ)),
        mul_ne_zero x.2 (Complex.exp_ne_zero _)⟩, by
      refine Continuous.subtype_mk ?_ _
      fun_prop⟩
  source' := by
    apply Subtype.ext
    simp
  target' := by
    apply Subtype.ext
    change (x : ℂ) * Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      * ((((1 : unitInterval) : ℝ)) : ℂ)) = (x : ℂ)
    have h1 : ((((1 : unitInterval) : ℝ)) : ℂ) = 1 := by simp
    rw [h1, mul_one, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]

@[simp] theorem powerLoop_apply (x : Cs) (n : ℤ) (t : unitInterval) :
    ((powerLoop x n t : Cs) : ℂ) =
      (x : ℂ) * Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℝ)) := rfl

theorem expP_straightLift (ζ : ℂ) (n : ℤ) (t : unitInterval) :
    expP (straightLift ζ n t) = powerLoop (expP ζ) n t := by
  apply Subtype.ext
  simp only [expP_apply, powerLoop_apply, straightLift_apply]
  rw [Complex.exp_add]

/-- The lift of a power loop is the corresponding straight path (uniqueness of lifts). -/
theorem liftPath_powerLoop_eq (ζ : ℂ) (n : ℤ) :
    isCoveringMap_expP.liftPath (powerLoop (expP ζ) n) ζ (Path.source (powerLoop (expP ζ) n))
      = (straightLift ζ n : C(unitInterval, ℂ)) := by
  let g₁ : unitInterval → ℂ := fun t =>
    isCoveringMap_expP.liftPath (powerLoop (expP ζ) n) ζ
      (Path.source (powerLoop (expP ζ) n)) t
  let g₂ : unitInterval → ℂ := fun t => straightLift ζ n t
  have hcont₁ : Continuous g₁ :=
    (isCoveringMap_expP.liftPath (powerLoop (expP ζ) n) ζ
      (Path.source (powerLoop (expP ζ) n))).continuous
  have hcont₂ : Continuous g₂ := (straightLift ζ n).continuous
  have hcomp : ⇑expP ∘ g₁ = ⇑expP ∘ g₂ := by
    funext t
    have hlift := congrFun (IsCoveringMap.liftPath_lifts isCoveringMap_expP
      (powerLoop (expP ζ) n) ζ (Path.source (powerLoop (expP ζ) n))) t
    simp only [Function.comp_apply] at hlift
    show expP (g₁ t) = expP (g₂ t)
    rw [hlift, expP_straightLift]
    rfl
  have h0 : g₁ 0 = g₂ 0 := by
    show isCoveringMap_expP.liftPath (powerLoop (expP ζ) n) ζ _ 0 = straightLift ζ n 0
    rw [IsCoveringMap.liftPath_zero]
    simp
  have h := isCoveringMap_expP.eq_of_comp_eq hcont₁ hcont₂ hcomp (0 : unitInterval) h0
  apply ContinuousMap.ext
  intro t
  exact congrFun h t

theorem liftPath_powerLoop_apply (ζ : ℂ) (n : ℤ) :
    (isCoveringMap_expP.liftPath (powerLoop (expP ζ) n) ζ (Path.source (powerLoop (expP ζ) n))) 1
      = ζ + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h := liftPath_powerLoop_eq ζ n
  rw [h]
  simp [straightLift_apply]

/-- Every loop in `ℂ ∖ {0}` based at `expP ζ` is homotopic to `powerLoop (expP ζ) n`, where the
integer `n` is the "winding number" read off from the endpoint of the lift. -/
theorem homotopic_powerLoop {ζ : ℂ} (γ : Path (expP ζ) (expP ζ))
    {n : ℤ} (hn : (isCoveringMap_expP.liftPath γ ζ (Path.source γ)) 1
      = ζ + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    γ.Homotopic (powerLoop (expP ζ) n) := by
  refine homotopic_of_lift_endpoints_eq (ζ := ζ) ?_
  rw [hn, liftPath_powerLoop_apply]

/-- The "winding number" of a loop, read off from the endpoint of its lift. -/
theorem exists_int_lift_endpoint {ζ : ℂ} (γ : Path (expP ζ) (expP ζ)) :
    ∃ n : ℤ, (isCoveringMap_expP.liftPath γ ζ (Path.source γ)) 1
      = ζ + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h : Complex.exp ((isCoveringMap_expP.liftPath γ ζ (Path.source γ)) 1) = Complex.exp ζ := by
    have hlift := congrFun (IsCoveringMap.liftPath_lifts isCoveringMap_expP γ ζ
      (Path.source γ)) 1
    simp only [Function.comp_apply] at hlift
    rw [← expP_apply, hlift]
    change ((γ 1 : Cs) : ℂ) = Complex.exp ζ
    rw [Path.target γ, expP_apply]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  exact ⟨n, hn⟩

/-! ## Homotopy of loops with explicitly given lifts -/

/-- **Master lemma, general form.**  If two loops based at `expP ζ` have lifts `η₁`, `η₂` which are
paths from `ζ` to (propositionally equal) endpoints, then the loops are homotopic. -/
theorem homotopic_of_lifts {ζ ζ₁ ζ₂ : ℂ} {γ₁ γ₂ : Path (expP ζ) (expP ζ)}
    (η₁ : Path ζ ζ₁) (η₂ : Path ζ ζ₂) (h₁ : ∀ t, expP (η₁ t) = γ₁ t)
    (h₂ : ∀ t, expP (η₂ t) = γ₂ t) (hζ : ζ₁ = ζ₂) :
    γ₁.Homotopic γ₂ := by
  -- `η` and the chosen lift of `γ` are both lifts from `ζ`, hence equal
  have key : ∀ {ζ₀ : ℂ} (γ : Path (expP ζ) (expP ζ)) (η : Path ζ ζ₀)
      (h : ∀ t, expP (η t) = γ t),
      (isCoveringMap_expP.liftPath γ ζ (Path.source γ)) 1 = η 1 := by
    intro ζ₀ γ η h
    have hc₁ : Continuous (fun t : unitInterval => isCoveringMap_expP.liftPath γ ζ
        (Path.source γ) t) := (isCoveringMap_expP.liftPath γ ζ (Path.source γ)).continuous
    have hc₂ : Continuous (fun t : unitInterval => η t) := η.continuous
    have hcomp : (⇑expP ∘ fun t : unitInterval => isCoveringMap_expP.liftPath γ ζ
        (Path.source γ) t) = (⇑expP ∘ fun t : unitInterval => η t) := by
      funext t
      simp only [Function.comp_apply]
      have h0 := congrFun (IsCoveringMap.liftPath_lifts isCoveringMap_expP γ ζ
        (Path.source γ)) t
      simp only [Function.comp_apply] at h0
      exact h0.trans (h t).symm
    have h0 : isCoveringMap_expP.liftPath γ ζ (Path.source γ) 0 = η 0 := by
      rw [IsCoveringMap.liftPath_zero, Path.source]
    have hcm : (isCoveringMap_expP.liftPath γ ζ (Path.source γ) : C(unitInterval, ℂ))
        = (η : C(unitInterval, ℂ)) := by
      apply ContinuousMap.ext
      intro t
      exact congrFun (isCoveringMap_expP.eq_of_comp_eq hc₁ hc₂ hcomp
        (0 : unitInterval) h0) t
    exact congrArg (fun p : C(unitInterval, ℂ) => p 1) hcm
  have e₁ : (isCoveringMap_expP.liftPath γ₁ ζ (Path.source γ₁)) 1 = ζ₁ :=
    (key γ₁ η₁ h₁).trans (Path.target η₁)
  have e₂ : (isCoveringMap_expP.liftPath γ₂ ζ (Path.source γ₂)) 1 = ζ₂ :=
    (key γ₂ η₂ h₂).trans (Path.target η₂)
  refine homotopic_of_lift_endpoints_eq (ζ := ζ) ?_
  rw [e₁, e₂, hζ]

/-- Shifting the base point of a power loop does not change the loop. -/
theorem expP_straightLift_shift (ζ : ℂ) (m n : ℤ) (t : unitInterval) :
    expP (straightLift (ζ + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) n t)
      = powerLoop (expP ζ) n t := by
  apply Subtype.ext
  simp only [expP_apply, powerLoop_apply, straightLift_apply]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I,
    one_zpow]
  ring

/-- **Additivity of power loops:** the concatenation of `powerLoop m` and `powerLoop n` is
homotopic to `powerLoop (m+n)`. -/
theorem powerLoop_trans_homotopic {ζ : ℂ} (m n : ℤ) :
    ((powerLoop (expP ζ) m).trans (powerLoop (expP ζ) n)).Homotopic
      (powerLoop (expP ζ) (m + n)) := by
  refine homotopic_of_lifts (ζ₁ := ζ + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
    (η₁ := (straightLift ζ m).trans
      (straightLift (ζ + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) n))
    (η₂ := straightLift ζ (m + n)) ?_ ?_ ?_
  · intro t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with h
    · exact expP_straightLift ζ m _
    · exact expP_straightLift_shift ζ m n _
  · intro t
    exact expP_straightLift ζ (m + n) t
  · push_cast
    ring

/-! ## `π₁(ℂ ∖ {0})` is generated by the standard loop -/

theorem powerLoop_zero_eq {ζ : ℂ} : powerLoop (expP ζ) 0 = Path.refl (expP ζ) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  simp [powerLoop_apply]

/-- The class of the `n`-th power loop, as an element of the fundamental group. -/
def powerClass (ζ : ℂ) (n : ℤ) : FundamentalGroup Cs (expP ζ) :=
  Path.Homotopic.Quotient.mk (powerLoop (expP ζ) n)

/-- The standard generator of `π₁(ℂ ∖ {0})` at the base point `expP ζ`. -/
def stdGen (ζ : ℂ) : FundamentalGroup Cs (expP ζ) :=
  powerClass ζ 1

theorem powerClass_zero (ζ : ℂ) : powerClass ζ 0 = 1 := by
  rw [powerClass, powerLoop_zero_eq, FundamentalGroup.one_def]
  rfl

/-- **Additivity** of the power classes, in the fundamental group. -/
theorem powerClass_mul (ζ : ℂ) (m n : ℤ) : powerClass ζ m * powerClass ζ n = powerClass ζ (m + n) := by
  rw [powerClass, powerClass, FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.mk_trans]
  refine Path.Homotopic.Quotient.eq.mpr ?_
  have h := powerLoop_trans_homotopic (ζ := ζ) n m
  rwa [add_comm] at h

/-- **The power classes are the powers of the standard generator.** -/
theorem powerClass_zpow (ζ : ℂ) (n : ℤ) : powerClass ζ n = (stdGen ζ) ^ n := by
  have hgen : powerClass ζ 1 = stdGen ζ := rfl
  refine Int.induction_on n ?_ ?_ ?_
  · rw [zpow_zero, powerClass_zero]
  · intro i ih
    rw [show ((i : ℤ) + 1) = (i : ℤ) + 1 from rfl, ← powerClass_mul, hgen, ih, zpow_add_one]
  · intro i ih
    have h := powerClass_mul ζ (-(i : ℤ) - 1) 1
    have h1 : (-(i : ℤ) - 1) + 1 = -(i : ℤ) := by ring
    rw [h1, hgen] at h
    have h2 : powerClass ζ (-(i : ℤ) - 1) = powerClass ζ (-(i : ℤ)) * (stdGen ζ)⁻¹ := by
      have hh := congrArg (fun u : FundamentalGroup Cs (expP ζ) => u * (stdGen ζ)⁻¹) h
      rw [mul_assoc, mul_inv_cancel, mul_one] at hh
      exact hh
    rw [h2, ih, show (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) from by ring, zpow_add, zpow_neg_one]

/-- **`π₁(ℂ ∖ {0})` is cyclic**: the class of the standard loop generates the fundamental group. -/
theorem pi1_plane_cyclic (ζ : ℂ) : Subgroup.closure ({stdGen ζ} : Set _) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  induction g using Quotient.inductionOn with
  | h γ =>
    obtain ⟨n, hn⟩ := exists_int_lift_endpoint (ζ := ζ) γ
    refine Subgroup.mem_closure_singleton.mpr ⟨n, ?_⟩
    rw [← powerClass_zpow]
    exact (Path.Homotopic.Quotient.eq.mpr (homotopic_powerLoop γ hn)).symm

end

end Work.SphereJordan
