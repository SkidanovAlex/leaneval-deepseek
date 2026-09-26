import Mathlib
import Submission.Commons.Topology.Plane.loop_of_strip_lift_not_nullhomotopic

/-!
# A strip path avoiding a closed set produces an essential loop

Given a path `γ` in the strip `ℝ × ℝ` (coordinates `(angle, radius)`) whose first
coordinate advances by `2π` over the parameter interval and whose second coordinate
stays positive, together with the hypothesis that the "exponential" projection
`q ↦ q.2 * exp (q.1 * I)` of the path avoids a closed set `L ⊆ ℂ`, we produce a loop
`γ' : Circle → {z : ℂ // z ≠ 0}` whose values avoid `L` and which is not nullhomotopic.

The loop is the descent of the projected path to the circle; it has winding number `1`
around the origin, so it is essential.  The essentiality is certified by exhibiting a
continuous lift `G : ℝ → ℝ × ℝ` of `γ' ∘ Circle.exp` whose angle coordinate advances by
`2π` over one period, and applying the commons lemma
`Commons.Topology.Plane.loop_of_strip_lift_not_nullhomotopic`.
-/

namespace Commons.Topology.Plane

open Set Function


/-- The projection of a real number onto the interval `[0,1]`. -/
private noncomputable def clampI (x : ℝ) : Set.Icc (0 : ℝ) 1 := Set.projIcc 0 1 (by norm_num) x

private lemma continuous_clampI : Continuous clampI := continuous_projIcc (h := by norm_num)

/-- The angle coordinate of the clamped strip path. -/
private noncomputable def stripTheta (γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (x : ℝ) : ℝ :=
  (γ (clampI x)).1

/-- The radius coordinate of the clamped strip path. -/
private noncomputable def stripRho (γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (x : ℝ) : ℝ :=
  (γ (clampI x)).2

private lemma continuous_stripTheta (γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) :
    Continuous (stripTheta γ) :=
  continuous_fst.comp (γ.continuous.comp continuous_clampI)

private lemma continuous_stripRho (γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) :
    Continuous (stripRho γ) :=
  continuous_snd.comp (γ.continuous.comp continuous_clampI)

/-- `exp (2π n I) = 1` on `Circle`, for integral `n`. -/
private lemma circle_exp_two_pi_mul_int (n : ℤ) :
    Circle.exp (2 * Real.pi * (n : ℝ)) = 1 := by
  have h : 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) := by ring
  rw [h, Circle.exp_intCast_mul, Circle.exp_two_pi, one_zpow]

/-- the complex form of `circle_exp_two_pi_mul_int`. -/
private lemma complex_exp_two_pi_mul_int (n : ℤ) :
    Complex.exp (((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [← Circle.coe_exp (2 * Real.pi * (n : ℝ)), circle_exp_two_pi_mul_int n, Circle.coe_one]

/-- `Int.fract` is the canonical representative in `AddCircle 1`. -/
private lemma coe_fract_eq_addCircle_one (s : ℝ) :
    (↑(Int.fract s) : AddCircle (1 : ℝ)) = (↑s : AddCircle (1 : ℝ)) := by
  conv_rhs => rw [← Int.fract_add_floor s]
  rw [AddCircle.coe_add]
  have hz : (↑(⌊s⌋ : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have h1 : (⌊s⌋ : ℝ) = (⌊s⌋ : ℤ) • (1 : ℝ) := by rw [zsmul_eq_mul, mul_one]
    rw [h1, AddCircle.coe_zsmul, AddCircle.coe_period (1 : ℝ), smul_zero]
  rw [hz, add_zero]

/-- Shifting the angle by `2π` does not change `exp (θ I)`. -/
private lemma exp_add_two_pi (z : ℝ) :
    Complex.exp (((z + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((z : ℝ) : ℂ) * Complex.I) := by
  rw [show (((z + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
        = ((z : ℂ) * Complex.I) + (((2 * Real.pi : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
  rw [Complex.exp_add]
  have h2 : Complex.exp ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) = 1 := by
    rw [← Circle.coe_exp (2 * Real.pi), Circle.exp_two_pi, Circle.coe_one]
  rw [h2, mul_one]

theorem exists_loop_of_strip_path {L : Set ℂ} (hL : IsClosed L)
    (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (h1 : (γ 1).1 = (γ 0).1 + 2 * Real.pi)
    (h2 : (γ 1).2 = (γ 0).2) (ha : ∀ t, 0 < (γ t).2)
    (havoid : ∀ t, ((γ t).2 : ℂ) * Complex.exp (((γ t).1 : ℂ) * Complex.I) ∉ L) :
    ∃ γ' : C(Circle, {z : ℂ // z ≠ 0}), (∀ t, (γ' t : ℂ) ∉ L) ∧ ¬ γ'.Nullhomotopic := by
  have _hL := hL
  let θ := stripTheta γ
  let ρ := stripRho γ
  have hθc : Continuous θ := continuous_stripTheta γ
  have hρc : Continuous ρ := continuous_stripRho γ
  have hθ0 : θ 0 = (γ 0).1 := by simp only [θ, stripTheta, clampI, Set.projIcc_left]; rfl
  have hθ1 : θ 1 = (γ 1).1 := by simp only [θ, stripTheta, clampI, Set.projIcc_right]; rfl
  have hρ0 : ρ 0 = (γ 0).2 := by simp only [ρ, stripRho, clampI, Set.projIcc_left]; rfl
  have hρ1 : ρ 1 = (γ 1).2 := by simp only [ρ, stripRho, clampI, Set.projIcc_right]; rfl
  have hρpos : ∀ x, 0 < ρ x := fun x => ha (clampI x)
  -- the complex value of the strip path, clamped to the fundamental domain
  let v : ℝ → ℂ := fun x => ((ρ x : ℝ) : ℂ) * Complex.exp (((θ x : ℝ) : ℂ) * Complex.I)
  have hv : Continuous v :=
    (Complex.continuous_ofReal.comp hρc).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hθc).mul continuous_const))
  have hne : ∀ x, v x ≠ 0 := fun x =>
    mul_ne_zero (by exact_mod_cast (ne_of_gt (hρpos x))) (Complex.exp_ne_zero _)
  let f : ℝ → {z : ℂ // z ≠ 0} := fun x => ⟨v x, hne x⟩
  have hfc : Continuous f := Continuous.subtype_mk hv hne
  have hf01 : f 0 = f 1 := by
    apply Subtype.ext
    simp only [f, v]
    rw [hρ0, hρ1, hθ0, hθ1, h2, h1]
    rw [exp_add_two_pi]
  -- the loop on the additive circle, and its transport to `Circle`
  let γ'' : C(AddCircle (1:ℝ), {z : ℂ // z ≠ 0}) :=
    ⟨AddCircle.liftIco 1 0 f, AddCircle.liftIco_zero_continuous hf01 hfc.continuousOn⟩
  let hC : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num : (1:ℝ) ≠ 0)
  let γ' : C(Circle, {z : ℂ // z ≠ 0}) := γ''.comp ⟨hC.symm, hC.symm.continuous⟩
  -- the lift of `γ' ∘ Circle.exp`
  let wθ : ℝ → ℝ := fun x => θ x - 2*Real.pi*x
  have hwθc : Continuous wθ := hθc.sub (continuous_const.mul continuous_id)
  have hwθ01 : wθ 0 = wθ 1 := by
    simp only [wθ]
    rw [hθ0, hθ1, h1]
    ring
  have hρ01 : ρ 0 = ρ 1 := by rw [hρ0, hρ1, h2]
  let ρbar : C(AddCircle (1:ℝ), ℝ) :=
    ⟨AddCircle.liftIco 1 0 ρ, AddCircle.liftIco_zero_continuous hρ01 hρc.continuousOn⟩
  let wbar : C(AddCircle (1:ℝ), ℝ) :=
    ⟨AddCircle.liftIco 1 0 wθ, AddCircle.liftIco_zero_continuous hwθ01 hwθc.continuousOn⟩
  let sfun : ℝ → AddCircle (1:ℝ) := fun τ => (↑(τ / (2*Real.pi)) : AddCircle (1:ℝ))
  have hsfun_c : Continuous sfun := (AddCircle.continuous_mk' 1).comp (continuous_id.div_const _)
  let Wfun : ℝ → ℝ := fun τ => wbar (sfun τ)
  let Rfun : ℝ → ℝ := fun τ => ρbar (sfun τ)
  have hWc : Continuous Wfun := wbar.continuous.comp hsfun_c
  have hRc : Continuous Rfun := ρbar.continuous.comp hsfun_c
  let G : C(ℝ, ℝ×ℝ) := ⟨fun τ => (τ + Wfun τ, Rfun τ), (continuous_id.add hWc).prodMk hRc⟩
  have hρbar_pos : ∀ a : AddCircle (1:ℝ), 0 < ρbar a := by
    intro a
    obtain ⟨b, hb, hba⟩ := AddCircle.eq_coe_Ico (p := (1:ℝ)) a
    have hbIcc : b ∈ Set.Icc (0:ℝ) 1 := ⟨hb.1, hb.2.le⟩
    have h1' : ρbar a = ρ b := by
      rw [← hba]
      show AddCircle.liftIco 1 0 ρ (↑b) = ρ b
      exact AddCircle.liftIco_zero_coe_apply hb
    rw [h1']
    have h2' : ρ b = (γ ⟨b, hbIcc⟩).2 := by
      show (γ (clampI b)).2 = (γ ⟨b, hbIcc⟩).2
      rw [show clampI b = ⟨b, hbIcc⟩ from Set.projIcc_of_mem (by norm_num) hbIcc]
    rw [h2']
    exact ha ⟨b, hbIcc⟩
  have hGpos : ∀ τ, 0 < (G τ).2 := by
    intro τ
    show 0 < ρbar (sfun τ)
    exact hρbar_pos _
  have hWper : ∀ τ, Wfun (τ + 2*Real.pi) = Wfun τ := by
    intro τ
    show wbar (sfun (τ + 2*Real.pi)) = wbar (sfun τ)
    congr 1
    show (↑((τ + 2*Real.pi)/(2*Real.pi)) : AddCircle (1:ℝ)) = (↑(τ/(2*Real.pi)) : AddCircle (1:ℝ))
    rw [show (τ + 2*Real.pi)/(2*Real.pi) = τ/(2*Real.pi) + 1 by field_simp]
    exact AddCircle.coe_add_period (1:ℝ) (τ/(2*Real.pi))
  have hRper : ∀ τ, Rfun (τ + 2*Real.pi) = Rfun τ := by
    intro τ
    show ρbar (sfun (τ + 2*Real.pi)) = ρbar (sfun τ)
    congr 1
    show (↑((τ + 2*Real.pi)/(2*Real.pi)) : AddCircle (1:ℝ)) = (↑(τ/(2*Real.pi)) : AddCircle (1:ℝ))
    rw [show (τ + 2*Real.pi)/(2*Real.pi) = τ/(2*Real.pi) + 1 by field_simp]
    exact AddCircle.coe_add_period (1:ℝ) (τ/(2*Real.pi))
  have hGper : ∀ τ, G (τ + 2*Real.pi) = ((G τ).1 + 2*Real.pi, (G τ).2) := by
    intro τ
    have h1' := hWper τ
    have h2' := hRper τ
    show (((τ + 2*Real.pi) + Wfun (τ + 2*Real.pi), Rfun (τ + 2*Real.pi))
        = ((τ + Wfun τ) + 2*Real.pi, Rfun τ))
    rw [h1', h2']
    refine Prod.ext ?_ ?_ <;> ring
  have hG_lift : ∀ τ, ((G τ).2 : ℂ) * Complex.exp (((G τ).1 : ℂ) * Complex.I)
      = (γ' (Circle.exp τ) : ℂ) := by
    intro τ
    show ((Rfun τ : ℝ) : ℂ) * Complex.exp (((τ + Wfun τ : ℝ) : ℂ) * Complex.I)
        = (γ' (Circle.exp τ) : ℂ)
    let s : ℝ := τ / (2*Real.pi)
    let u : ℝ := Int.fract s
    have huIco : u ∈ Set.Ico (0:ℝ) 1 :=
      ⟨by rw [show u = Int.fract s from rfl]; exact Int.fract_nonneg s,
       by rw [show u = Int.fract s from rfl]; exact Int.fract_lt_one s⟩
    have hcoe : (↑u : AddCircle (1:ℝ)) = (↑s : AddCircle (1:ℝ)) := by
      show (↑(Int.fract s) : AddCircle (1:ℝ)) = (↑(τ/(2*Real.pi)) : AddCircle (1:ℝ))
      exact coe_fract_eq_addCircle_one s
    have hR : Rfun τ = ρ u := by
      show ρbar (↑s) = ρ u
      rw [← hcoe]
      show AddCircle.liftIco 1 0 ρ (↑u) = ρ u
      exact AddCircle.liftIco_zero_coe_apply huIco
    have hW : Wfun τ = wθ u := by
      show wbar (↑s) = wθ u
      rw [← hcoe]
      show AddCircle.liftIco 1 0 wθ (↑u) = wθ u
      exact AddCircle.liftIco_zero_coe_apply huIco
    have hsτ : τ = 2*Real.pi*s := by
      show τ = 2*Real.pi*(τ/(2*Real.pi))
      field_simp
    have hexpτ : Circle.exp τ = hC (↑s) := by
      rw [AddCircle.homeomorphCircle_apply]
      show Circle.exp τ = AddCircle.toCircle (↑s : AddCircle (1:ℝ))
      rw [AddCircle.toCircle_apply_mk]
      congr 1
      rw [show 2 * Real.pi / 1 * s = τ by rw [hsτ]; ring]
    have hγ' : γ' (Circle.exp τ) = f u := by
      rw [hexpτ]
      show γ'' (hC.symm (hC (↑s))) = f u
      rw [hC.symm_apply_apply]
      show AddCircle.liftIco 1 0 f (↑s) = f u
      rw [← hcoe]
      exact AddCircle.liftIco_zero_coe_apply huIco
    rw [hR, hW, hγ']
    show ((ρ u : ℝ) : ℂ) * Complex.exp (((τ + (θ u - 2*Real.pi*u) : ℝ) : ℂ) * Complex.I)
        = ((ρ u : ℝ) : ℂ) * Complex.exp (((θ u : ℝ) : ℂ) * Complex.I)
    have hexp : Complex.exp (((τ + (θ u - 2*Real.pi*u) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((θ u : ℝ) : ℂ) * Complex.I) := by
      have hs_decomp : s = u + (⌊s⌋ : ℝ) := by
        show τ/(2*Real.pi) = Int.fract s + ↑⌊s⌋
        rw [Int.fract_add_floor]
      have htau : τ = 2*Real.pi*(u + (⌊s⌋:ℝ)) := by
        rw [hsτ]
        exact congrArg (fun x => 2*Real.pi*x) hs_decomp
      rw [show τ + (θ u - 2*Real.pi*u) = θ u + 2*Real.pi*(⌊s⌋:ℝ) by
            rw [htau]; ring]
      rw [show (((θ u + 2*Real.pi*(⌊s⌋:ℝ) : ℝ) : ℂ) * Complex.I)
            = (θ u : ℂ) * Complex.I + (((2*Real.pi*(⌊s⌋:ℝ) : ℝ)) : ℂ) * Complex.I by
          push_cast; ring]
      rw [Complex.exp_add, complex_exp_two_pi_mul_int ⌊s⌋, mul_one]
    rw [hexp]
  -- the loop avoids `L`
  have havoide : ∀ t : Circle, (γ' t : ℂ) ∉ L := by
    intro t
    obtain ⟨b, hbIco, hba⟩ := AddCircle.eq_coe_Ico (p := (1:ℝ)) (hC.symm t)
    have hbIcc : b ∈ Set.Icc (0:ℝ) 1 := ⟨hbIco.1, hbIco.2.le⟩
    have hval : γ' t = f b := by
      show γ'' (hC.symm t) = f b
      rw [← hba]
      show AddCircle.liftIco 1 0 f (↑b) = f b
      exact AddCircle.liftIco_zero_coe_apply hbIco
    rw [hval]
    show (((ρ b : ℝ) : ℂ) * Complex.exp (((θ b : ℝ) : ℂ) * Complex.I)) ∉ L
    have h1' : ρ b = (γ ⟨b, hbIcc⟩).2 := by
      show (γ (clampI b)).2 = (γ ⟨b, hbIcc⟩).2
      rw [show clampI b = ⟨b, hbIcc⟩ from Set.projIcc_of_mem (by norm_num) hbIcc]
    have h2' : θ b = (γ ⟨b, hbIcc⟩).1 := by
      show (γ (clampI b)).1 = (γ ⟨b, hbIcc⟩).1
      rw [show clampI b = ⟨b, hbIcc⟩ from Set.projIcc_of_mem (by norm_num) hbIcc]
    rw [h1', h2']
    exact havoid ⟨b, hbIcc⟩
  refine ⟨γ', havoide, ?_⟩
  exact loop_of_strip_lift_not_nullhomotopic (γ := γ') G hGpos hG_lift hGper

end Commons.Topology.Plane
