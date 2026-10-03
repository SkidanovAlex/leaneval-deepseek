import Mathlib
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.defs

namespace Work.BasinSC.CoverDisc

open Set Metric Filter Topology Function

/-! ## Part 1: the universal covering `t ↦ exp (-t)` of the punctured disc

The right half-plane `U = {t : ℂ | 0 < t.re}` is convex, hence contractible.  The map
`u t = exp (-t)` is a covering map `U → 𝔻*` whose deck group is the group of translations
by multiples of `2 * π * I`. -/

/-- The right half plane, model of the universal cover of `𝔻*`. -/
def U : Set ℂ := {t : ℂ | 0 < t.re}

theorem U_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re

theorem U_convex : Convex ℝ U := by
  have h : U = ⇑(Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' Set.Ioi 0 := rfl
  rw [h]
  exact (convex_Ioi (0 : ℝ)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)

theorem U_nonempty : U.Nonempty := ⟨1, by norm_num [U]⟩

instance : ContractibleSpace ↥U := Convex.contractibleSpace U_convex U_nonempty
instance : SimplyConnectedSpace ↥U := inferInstance
instance : PathConnectedSpace ↥U := inferInstance
instance : LocallyPathConnectedSpace ↥U := U_open.locallyPathConnectedSpace

/-- The period `2 * π * I` of the exponential. -/
noncomputable def period : ℂ := 2 * Real.pi * Complex.I

theorem period_re : period.re = 0 := by simp [period]

/-- Translation of the right half plane by an integer multiple of `2 * π * I`. -/
noncomputable def Ushift (n : ℤ) (t : ↥U) : ↥U :=
  ⟨(t : ℂ) + (n : ℂ) * period, by
    have h : ((t : ℂ) + (n : ℂ) * period).re = (t : ℂ).re := by
      simp [period, Complex.add_re, Complex.mul_re]
    show 0 < ((t : ℂ) + (n : ℂ) * period).re
    rw [h]; exact t.2⟩

theorem Ushift_zero (t : ↥U) : Ushift 0 t = t := by ext; simp [Ushift]

theorem Ushift_add (m n : ℤ) (t : ↥U) : Ushift (m + n) t = Ushift m (Ushift n t) := by
  ext; simp only [Ushift, Subtype.coe_mk, Int.cast_add]; ring

theorem Ushift_coe (n : ℤ) (t : ↥U) : ((Ushift n t : ↥U) : ℂ) = (t : ℂ) + (n : ℂ) * period :=
  rfl

/-! ### The covering map -/

theorem isCoveringMap_exp_neg :
    IsCoveringMap (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) :=
  Complex.isCoveringMap_exp

/-- `z ↦ exp (-z) : ℂ → ℂ*` is a covering map. -/
noncomputable def E : ℂ → {w : ℂ // w ≠ 0} :=
  (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ (Homeomorph.neg ℂ)

theorem E_apply (z : ℂ) : (E z : ℂ) = Complex.exp (-z) := rfl

theorem E_isCoveringMap : IsCoveringMap E :=
  Complex.isCoveringMap_exp.comp_homeomorph (Homeomorph.neg ℂ)

/-- The open unit disc inside `ℂ*`. -/
def sdisc : Set {w : ℂ // w ≠ 0} := {w | ‖(w : ℂ)‖ < 1}

theorem E_preimage_sdisc : E ⁻¹' sdisc = U := by
  ext z
  simp only [sdisc, U, Set.mem_preimage, Set.mem_ofPred_eq, E_apply, Complex.norm_exp,
    Complex.neg_re, Real.exp_lt_one_iff, neg_lt_zero]

/-- `↥sdisc ≃ₜ 𝔻*`. -/
noncomputable def sdiscHomeo : ↥sdisc ≃ₜ ↥puncturedDisc where
  toFun w := ⟨(w : {w : ℂ // w ≠ 0}).1, (w : {w : ℂ // w ≠ 0}).2, w.2⟩
  invFun w := ⟨⟨(w : ℂ), w.2.1⟩, w.2.2⟩
  left_inv w := by ext; rfl
  right_inv w := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The universal covering `u : U → 𝔻*`, `u t = exp (-t)`. -/
noncomputable def u : ↥U → ↥puncturedDisc :=
  sdiscHomeo ∘ (sdisc.restrictPreimage E) ∘ (Homeomorph.setCongr E_preimage_sdisc).symm

theorem u_val (t : ↥U) : ((u t : ↥puncturedDisc) : ℂ) = Complex.exp (-(t : ℂ)) := rfl

theorem u_isCoveringMap : IsCoveringMap u := by
  have h : IsCoveringMap ((sdisc.restrictPreimage E) ∘
      ⇑((Homeomorph.setCongr E_preimage_sdisc).symm)) :=
    (IsCoveringMap.restrictPreimage E_isCoveringMap sdisc).comp_homeomorph
      (Homeomorph.setCongr E_preimage_sdisc).symm
  have h2 : IsCoveringMap (fun t : ↥U =>
      sdiscHomeo ((sdisc.restrictPreimage E) ((Homeomorph.setCongr E_preimage_sdisc).symm t))) :=
    h.homeomorph_comp sdiscHomeo
  simpa [u, Function.comp_def] using h2

theorem u_Ushift (n : ℤ) (t : ↥U) : u (Ushift n t) = u t := by
  apply Subtype.ext
  simp only [u_val, Ushift]
  have h1 : -((t : ℂ) + (n : ℂ) * period) =
      -(t : ℂ) + ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [period]; push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem u_eq_iff (t t' : ↥U) : u t = u t' ↔ ∃ n : ℤ, t' = Ushift n t := by
  constructor
  · intro h
    have h' : Complex.exp (-(t : ℂ)) = Complex.exp (-(t' : ℂ)) := by
      have := congrArg (fun x : ↥puncturedDisc => (x : ℂ)) h
      simpa [u_val] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h'
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [Ushift]
    have h3 : -(t' : ℂ) = -(t : ℂ) - (n : ℂ) * period := by
      have hh := hn
      simp only [period] at hh ⊢
      rw [hh]; ring
    have h4 : (t' : ℂ) = (t : ℂ) + (n : ℂ) * period := by
      have := congrArg Neg.neg h3
      simpa [add_comm] using this
    exact h4
  · rintro ⟨n, rfl⟩
    exact (u_Ushift n t).symm

theorem continuous_Ushift (n : ℤ) : Continuous (Ushift n) := by
  apply Continuous.subtype_mk
  show Continuous fun t : ↥U => (t : ℂ) + (n : ℂ) * period
  exact continuous_subtype_val.add continuous_const


/-! ## Part 2: the lift of `u` through `q` and the associated `ℤ`-action -/

section Main

variable {Z : Type*} [TopologicalSpace Z] [PathConnectedSpace Z] {q : Z → ↥puncturedDisc}

theorem u_continuous : Continuous u := u_isCoveringMap.continuous

/-- The basepoint `1` of the right half plane. -/
def t0 : ↥U := ⟨1, by norm_num [U]⟩

theorem u_surjective : Function.Surjective u := by
  intro w
  refine ⟨⟨-Complex.log (w : ℂ), ?_⟩, ?_⟩
  · show 0 < (-Complex.log (w : ℂ)).re
    rw [Complex.neg_re, Complex.log_re]
    exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr w.2.1) w.2.2)
  · apply Subtype.ext
    show Complex.exp (-(-Complex.log (w : ℂ))) = (w : ℂ)
    rw [neg_neg, Complex.exp_log w.2.1]

variable (hcov : IsCoveringMap q) (t₀ : ↥U)

/-- The unique lift of `u` through `q` sending `t₀` to `v`. -/
noncomputable def liftAt (v : ↥(q ⁻¹' {u t₀})) : C(↥U, Z) :=
  (hcov.existsUnique_continuousMap_lifts (⟨u, u_continuous⟩ : C(↥U, ↥puncturedDisc))
    t₀ v.1 (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, ContinuousMap.coe_mk] using v.2)).exists.choose

theorem liftAt_self (v : ↥(q ⁻¹' {u t₀})) : liftAt hcov t₀ v t₀ = v.1 :=
  ((hcov.existsUnique_continuousMap_lifts (⟨u, u_continuous⟩ : C(↥U, ↥puncturedDisc))
    t₀ v.1 (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, ContinuousMap.coe_mk] using v.2)).exists.choose_spec).1

theorem liftAt_mem (v : ↥(q ⁻¹' {u t₀})) (s : ↥U) : q (liftAt hcov t₀ v s) = u s :=
  congrFun ((hcov.existsUnique_continuousMap_lifts (⟨u, u_continuous⟩ : C(↥U, ↥puncturedDisc))
    t₀ v.1 (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, ContinuousMap.coe_mk] using v.2)).exists.choose_spec).2 s

/-- Translation of the fibre of `q` over `u t₀`, induced by the deck translations of `U`. -/
noncomputable def T (n : ℤ) (v : ↥(q ⁻¹' {u t₀})) : ↥(q ⁻¹' {u t₀}) :=
  ⟨liftAt hcov t₀ v (Ushift n t₀), by
    rw [Set.mem_preimage, Set.mem_singleton_iff, liftAt_mem hcov t₀ v (Ushift n t₀), u_Ushift]⟩

theorem T_zero (v : ↥(q ⁻¹' {u t₀})) : T hcov t₀ 0 v = v := by
  apply Subtype.ext
  show liftAt hcov t₀ v (Ushift 0 t₀) = v.1
  rw [Ushift_zero, liftAt_self]

theorem T_key (w : ↥(q ⁻¹' {u t₀})) (m : ℤ) (s : ↥U) :
    liftAt hcov t₀ w (Ushift m s) = liftAt hcov t₀ (T hcov t₀ m w) s := by
  have hc1 : Continuous fun s : ↥U => liftAt hcov t₀ w (Ushift m s) :=
    (liftAt hcov t₀ w).continuous.comp (continuous_Ushift m)
  have hc2 : Continuous fun s : ↥U => liftAt hcov t₀ (T hcov t₀ m w) s :=
    (liftAt hcov t₀ (T hcov t₀ m w)).continuous
  have heq : q ∘ (fun s : ↥U => liftAt hcov t₀ w (Ushift m s)) =
      q ∘ (fun s : ↥U => liftAt hcov t₀ (T hcov t₀ m w) s) := by
    funext s
    simp only [Function.comp_apply]
    rw [liftAt_mem hcov t₀ w (Ushift m s), u_Ushift,
      liftAt_mem hcov t₀ (T hcov t₀ m w) s]
  have hpoint : liftAt hcov t₀ w (Ushift m t₀) =
      liftAt hcov t₀ (T hcov t₀ m w) t₀ := by
    rw [liftAt_self]
    rfl
  exact congrFun (IsCoveringMap.eq_of_comp_eq hcov hc1 hc2 heq t₀ hpoint) s

theorem T_add' (a b : ℤ) (v : ↥(q ⁻¹' {u t₀})) :
    T hcov t₀ (a + b) v = T hcov t₀ b (T hcov t₀ a v) := by
  apply Subtype.ext
  show liftAt hcov t₀ v (Ushift (a + b) t₀) = liftAt hcov t₀ (T hcov t₀ a v) (Ushift b t₀)
  rw [Ushift_add, T_key]

theorem T_add (m n : ℤ) (v : ↥(q ⁻¹' {u t₀})) :
    T hcov t₀ (m + n) v = T hcov t₀ m (T hcov t₀ n v) := by
  rw [add_comm m n]
  exact T_add' hcov t₀ n m v

variable (z₀ : Z) (hz : q z₀ = u t₀)

/-- The lift of `u` through `q` sending `t₀` to `z₀`. -/
noncomputable def baseLift : C(↥U, Z) := liftAt hcov t₀ ⟨z₀, hz⟩

theorem baseLift_self : baseLift hcov t₀ z₀ hz t₀ = z₀ :=
  liftAt_self hcov t₀ ⟨z₀, hz⟩

theorem baseLift_mem (s : ↥U) : q (baseLift hcov t₀ z₀ hz s) = u s :=
  liftAt_mem hcov t₀ ⟨z₀, hz⟩ s

theorem T_base (n : ℤ) : T hcov t₀ n ⟨z₀, hz⟩ =
    ⟨baseLift hcov t₀ z₀ hz (Ushift n t₀), by
      rw [Set.mem_preimage, Set.mem_singleton_iff, baseLift_mem hcov t₀ z₀ hz (Ushift n t₀),
        u_Ushift]⟩ := rfl

theorem T_base_val (n : ℤ) :
    ((T hcov t₀ n ⟨z₀, hz⟩ : ↥(q ⁻¹' {u t₀})) : Z) = baseLift hcov t₀ z₀ hz (Ushift n t₀) :=
  rfl

theorem T_base_surjective (v : ↥(q ⁻¹' {u t₀})) :
    ∃ n : ℤ, T hcov t₀ n ⟨z₀, hz⟩ = v := by
  let γ : Path z₀ v.1 := PathConnectedSpace.somePath z₀ v.1
  let α : C(unitInterval, ↥puncturedDisc) :=
    ⟨fun s => q (γ s), hcov.continuous.comp γ.continuous⟩
  have hα0 : α 0 = u t₀ := by
    show q (γ 0) = u t₀
    rw [γ.source, hz]
  let αt : C(unitInterval, ↥U) := u_isCoveringMap.liftPath α t₀ hα0
  have hαt0 : αt 0 = t₀ := u_isCoveringMap.liftPath_zero α t₀ hα0
  have hαt_lift : ∀ s, u (αt s) = α s := fun s =>
    congrFun (u_isCoveringMap.liftPath_lifts α t₀ hα0) s
  have hvt : u (αt 1) = u t₀ := by
    rw [hαt_lift 1]
    show q (γ 1) = u t₀
    rw [γ.target, v.2]
  obtain ⟨n, hn⟩ := (u_eq_iff t₀ (αt 1)).mp hvt.symm
  refine ⟨n, ?_⟩
  apply Subtype.ext
  show baseLift hcov t₀ z₀ hz (Ushift n t₀) = v.1
  rw [← hn]
  have hαz : α 0 = q z₀ := by rw [hα0, hz]
  have hΓ₁ : (⟨fun s => baseLift hcov t₀ z₀ hz (αt s),
      (baseLift hcov t₀ z₀ hz).continuous.comp αt.continuous⟩ : C(unitInterval, Z)) =
      hcov.liftPath α z₀ hαz := by
    rw [hcov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · funext s
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [baseLift_mem hcov t₀ z₀ hz (αt s), hαt_lift s]
    · simp only [ContinuousMap.coe_mk]
      rw [hαt0, baseLift_self]
  have hΓ₂ : (γ.toContinuousMap : C(unitInterval, Z)) = hcov.liftPath α z₀ hαz := by
    rw [hcov.eq_liftPath_iff']
    exact ⟨by funext s; rfl, γ.source⟩
  have : baseLift hcov t₀ z₀ hz (αt 1) = γ 1 := by
    have := congrFun (congrArg DFunLike.coe (hΓ₁.trans hΓ₂.symm)) 1
    simpa using this
  rw [this, γ.target]

/-- The `ℤ`-action on the fibre of `q` over `u t₀`. -/
noncomputable def TAct : AddAction ℤ ↥(q ⁻¹' {u t₀}) where
  vadd := T hcov t₀
  add_vadd := T_add hcov t₀
  zero_vadd := T_zero hcov t₀

theorem T_base_stabilizer (n : ℤ) :
    T hcov t₀ n ⟨z₀, hz⟩ = ⟨z₀, hz⟩ ↔
      ∀ t : ↥U, baseLift hcov t₀ z₀ hz (Ushift n t) = baseLift hcov t₀ z₀ hz t := by
  constructor
  · intro h t
    have h' : baseLift hcov t₀ z₀ hz (Ushift n t₀) = baseLift hcov t₀ z₀ hz t₀ := by
      have hh := congrArg (fun x : ↥(q ⁻¹' {u t₀}) => (x : Z)) h
      rw [T_base_val] at hh
      exact hh.trans (baseLift_self hcov t₀ z₀ hz).symm
    have hc1 : Continuous fun s : ↥U => baseLift hcov t₀ z₀ hz (Ushift n s) :=
      (baseLift hcov t₀ z₀ hz).continuous.comp (continuous_Ushift n)
    have hc2 : Continuous (baseLift hcov t₀ z₀ hz) := (baseLift hcov t₀ z₀ hz).continuous
    have heq : q ∘ (fun s : ↥U => baseLift hcov t₀ z₀ hz (Ushift n s)) =
        q ∘ (baseLift hcov t₀ z₀ hz : ↥U → Z) := by
      funext s
      simp only [Function.comp_apply]
      rw [baseLift_mem hcov t₀ z₀ hz (Ushift n s), u_Ushift,
        baseLift_mem hcov t₀ z₀ hz s]
    exact congrFun (IsCoveringMap.eq_of_comp_eq hcov hc1 hc2 heq t₀ h') t
  · intro h
    apply Subtype.ext
    show baseLift hcov t₀ z₀ hz (Ushift n t₀) = z₀
    rw [h t₀, baseLift_self]

theorem T_base_range :
    Set.range (fun n : ℤ => T hcov t₀ n ⟨z₀, hz⟩) = Set.univ := by
  ext v
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  exact T_base_surjective hcov t₀ z₀ hz v

/-- The deck group of the lift `baseLift` (a subgroup of the translations by `2 * π * I`). -/
noncomputable def Gamma : AddSubgroup ℤ where
  carrier := {n | ∀ t : ↥U, baseLift hcov t₀ z₀ hz (Ushift n t) = baseLift hcov t₀ z₀ hz t}
  zero_mem' := by intro t; rw [Ushift_zero]
  add_mem' := by
    intro n m hn hm t
    rw [Ushift_add, hn (Ushift m t), hm t]
  neg_mem' := by
    intro n hn t
    have h1 : Ushift n (Ushift (-n) t) = t := by rw [← Ushift_add, add_neg_cancel, Ushift_zero]
    have := hn (Ushift (-n) t)
    rw [h1] at this
    exact this.symm

theorem Gamma_index (d : ℕ) (hd : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) :
    (Gamma hcov t₀ z₀ hz).index = d := by
  letI : AddAction ℤ ↥(q ⁻¹' {u t₀}) := TAct hcov t₀
  have hstab : Gamma hcov t₀ z₀ hz =
      AddAction.stabilizer ℤ (⟨z₀, hz⟩ : ↥(q ⁻¹' {u t₀})) := by
    ext n
    rw [AddAction.mem_stabilizer_iff]
    exact (T_base_stabilizer hcov t₀ z₀ hz n).symm
  rw [hstab, AddAction.index_stabilizer]
  have horb : AddAction.orbit ℤ (⟨z₀, hz⟩ : ↥(q ⁻¹' {u t₀})) = Set.univ := by
    rw [AddAction.orbit]
    convert T_base_range hcov t₀ z₀ hz using 2
    ext n
    rfl
  rw [horb, Set.ncard_univ, Nat.card_coe_set_eq, hd (u t₀)]



theorem Gamma_eq_zmultiples (d : ℕ) (hdpos : 0 < d)
    (hd : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) :
    Gamma hcov t₀ z₀ hz = AddSubgroup.zmultiples (d : ℤ) := by
  have hidx : (Gamma hcov t₀ z₀ hz).index = d := Gamma_index hcov t₀ z₀ hz d hd
  have hmem : (d : ℤ) ∈ Gamma hcov t₀ z₀ hz := by
    have h1 := AddSubgroup.nsmul_index_mem (Gamma hcov t₀ z₀ hz) (1 : ℤ)
    rw [hidx] at h1
    simpa using h1
  have hle : AddSubgroup.zmultiples (d : ℤ) ≤ Gamma hcov t₀ z₀ hz :=
    AddSubgroup.zmultiples_le.mpr hmem
  refine le_antisymm ?_ hle
  rw [← AddSubgroup.relIndex_eq_one]
  have hrel : (AddSubgroup.zmultiples (d : ℤ)).relIndex (Gamma hcov t₀ z₀ hz) * d = d := by
    have h := AddSubgroup.relIndex_mul_index hle
    rw [hidx, Int.index_zmultiples, Int.natAbs_natCast] at h
    exact h
  refine Nat.eq_of_mul_eq_mul_left hdpos ?_
  rw [mul_one]
  exact (mul_comm d _).trans hrel

/-! ### The `d`-th root map `Φ` -/

/-- Scaling `t ↦ t / d` preserves the right half plane. -/
noncomputable def sigma (d : ℕ) (hd : 0 < d) (t : ↥U) : ↥U :=
  ⟨(t : ℂ) / (d : ℂ), by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hdC : (d : ℂ) = (((d : ℝ)) : ℂ) := by push_cast; rfl
    have h : ((t : ℂ) / (d : ℂ)).re = (t : ℂ).re / (d : ℝ) := by
      rw [Complex.div_re, Complex.normSq_apply, hdC, Complex.ofReal_re, Complex.ofReal_im]
      simp only [mul_zero, add_zero]
      field_simp
      ring
    show 0 < ((t : ℂ) / (d : ℂ)).re
    rw [h]
    exact div_pos t.2 hd'⟩

/-- Scaling `t ↦ d * t` preserves the right half plane. -/
noncomputable def sigmaInv (d : ℕ) (hd : 0 < d) (t : ↥U) : ↥U :=
  ⟨(d : ℂ) * (t : ℂ), by
    have h : ((d : ℂ) * (t : ℂ)).re = (d : ℝ) * (t : ℂ).re := by simp [Complex.mul_re]
    show 0 < ((d : ℂ) * (t : ℂ)).re
    rw [h]
    exact mul_pos (by exact_mod_cast hd) t.2⟩

theorem continuous_sigma (d : ℕ) (hd : 0 < d) : Continuous (sigma d hd) := by
  apply Continuous.subtype_mk
  show Continuous fun t : ↥U => (t : ℂ) / (d : ℂ)
  exact continuous_subtype_val.div_const _

theorem continuous_sigmaInv (d : ℕ) (hd : 0 < d) : Continuous (sigmaInv d hd) := by
  apply Continuous.subtype_mk
  show Continuous fun t : ↥U => (d : ℂ) * (t : ℂ)
  exact continuous_const.mul continuous_subtype_val

theorem sigma_left_inv (d : ℕ) (hd : 0 < d) (t : ↥U) : sigma d hd (sigmaInv d hd t) = t := by
  apply Subtype.ext
  show ((d : ℂ) * (t : ℂ)) / (d : ℂ) = (t : ℂ)
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hd
  field_simp

theorem sigma_right_inv (d : ℕ) (hd : 0 < d) (t : ↥U) : sigmaInv d hd (sigma d hd t) = t := by
  apply Subtype.ext
  show (d : ℂ) * ((t : ℂ) / (d : ℂ)) = (t : ℂ)
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hd
  field_simp

/-- The homeomorphism `t ↦ t / d` of the right half plane. -/
noncomputable def sigmaHomeo (d : ℕ) (hd : 0 < d) : ↥U ≃ₜ ↥U where
  toFun := sigma d hd
  invFun := sigmaInv d hd
  left_inv := sigma_right_inv d hd
  right_inv := sigma_left_inv d hd
  continuous_toFun := continuous_sigma d hd
  continuous_invFun := continuous_sigmaInv d hd

theorem sigma_Ushift (d : ℕ) (hd : 0 < d) (k : ℤ) (t : ↥U) :
    sigma d hd (Ushift (k * (d : ℤ)) t) = Ushift k (sigma d hd t) := by
  apply Subtype.ext
  show ((t : ℂ) + (((k * (d : ℤ)) : ℤ) : ℂ) * period) / (d : ℂ) =
    (t : ℂ) / (d : ℂ) + (k : ℂ) * period
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hd
  push_cast
  field_simp

/-- The `d`-th root of the universal cover: `Φ t = exp (-t/d)`. -/
noncomputable def Phi (d : ℕ) (hd : 0 < d) (t : ↥U) : ↥puncturedDisc := u (sigma d hd t)

theorem Phi_val (d : ℕ) (hd : 0 < d) (t : ↥U) :
    ((Phi d hd t : ↥puncturedDisc) : ℂ) = Complex.exp (-((sigma d hd t : ↥U) : ℂ)) :=
  u_val _

theorem Phi_pow (d : ℕ) (hd : 0 < d) (t : ↥U) :
    ((Phi d hd t : ↥puncturedDisc) : ℂ) ^ d = ((u t : ↥puncturedDisc) : ℂ) := by
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hd
  show (Complex.exp (-((sigma d hd t : ↥U) : ℂ))) ^ d = Complex.exp (-(t : ℂ))
  rw [← Complex.exp_nat_mul]
  congr 1
  show (d : ℂ) * (-(((sigma d hd t : ↥U) : ℂ))) = -(t : ℂ)
  rw [show ((sigma d hd t : ↥U) : ℂ) = (t : ℂ) / (d : ℂ) from rfl]
  field_simp

theorem Phi_Ushift (d : ℕ) (hd : 0 < d) (k : ℤ) (t : ↥U) :
    Phi d hd (Ushift (k * (d : ℤ)) t) = Phi d hd t := by
  show u (sigma d hd (Ushift (k * (d : ℤ)) t)) = u (sigma d hd t)
  rw [sigma_Ushift, u_Ushift]

theorem Phi_isOpenMap (d : ℕ) (hd : 0 < d) : IsOpenMap (Phi d hd) := by
  have h : IsOpenMap (u ∘ (sigmaHomeo d hd : ↥U ≃ₜ ↥U)) :=
    u_isCoveringMap.isOpenMap.comp (sigmaHomeo d hd).isOpenMap
  convert h using 1
  ext t
  rfl

theorem Phi_surjective (d : ℕ) (hd : 0 < d) : Function.Surjective (Phi d hd) := by
  intro w
  obtain ⟨t, ht⟩ := u_surjective w
  refine ⟨sigmaInv d hd t, ?_⟩
  show u (sigma d hd (sigmaInv d hd t)) = w
  rw [sigma_left_inv, ht]

theorem Phi_eq_iff (d : ℕ) (hd : 0 < d) (s t : ↥U) :
    Phi d hd s = Phi d hd t ↔ ∃ k : ℤ, t = Ushift (k * (d : ℤ)) s := by
  constructor
  · intro h
    have h' : u (sigma d hd s) = u (sigma d hd t) := h
    obtain ⟨n, hn⟩ := (u_eq_iff (sigma d hd s) (sigma d hd t)).mp h'
    refine ⟨n, ?_⟩
    have h2 := congrArg (sigmaInv d hd) hn
    rw [sigma_right_inv] at h2
    rw [h2]
    apply Subtype.ext
    show (d : ℂ) * (((sigma d hd s : ↥U) : ℂ) + (n : ℂ) * period) =
      (s : ℂ) + ((n * (d : ℤ) : ℤ) : ℂ) * period
    rw [show ((sigma d hd s : ↥U) : ℂ) = (s : ℂ) / (d : ℂ) from rfl]
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hd
    rw [mul_add, show (d : ℂ) * ((s : ℂ) / (d : ℂ)) = (s : ℂ) by field_simp]
    push_cast
    ring
  · rintro ⟨k, rfl⟩
    exact (Phi_Ushift d hd k s).symm

theorem Phi_well_def (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) {s t : ↥U}
    (h : baseLift hcov t₀ z₀ hz s = baseLift hcov t₀ z₀ hz t) :
    Phi d hd s = Phi d hd t := by
  have hu : u s = u t := by
    rw [← baseLift_mem hcov t₀ z₀ hz s, ← baseLift_mem hcov t₀ z₀ hz t, h]
  obtain ⟨n, hn⟩ := (u_eq_iff s t).mp hu
  have hmem : (d : ℤ) ∣ n := by
    have hpoint : baseLift hcov t₀ z₀ hz (Ushift n s) = baseLift hcov t₀ z₀ hz s := by
      rw [← hn]; exact h.symm
    have hc1 : Continuous fun r : ↥U => baseLift hcov t₀ z₀ hz (Ushift n r) :=
      (baseLift hcov t₀ z₀ hz).continuous.comp (continuous_Ushift n)
    have heq : q ∘ (fun r : ↥U => baseLift hcov t₀ z₀ hz (Ushift n r)) =
        q ∘ (baseLift hcov t₀ z₀ hz : ↥U → Z) := by
      funext r; simp only [Function.comp_apply]
      rw [baseLift_mem hcov t₀ z₀ hz (Ushift n r), u_Ushift,
        baseLift_mem hcov t₀ z₀ hz r]
    have hall := IsCoveringMap.eq_of_comp_eq hcov hc1
      (baseLift hcov t₀ z₀ hz).continuous heq s hpoint
    have hgam : n ∈ Gamma hcov t₀ z₀ hz := by
      intro r
      exact congrFun hall r
    rw [Gamma_eq_zmultiples hcov t₀ z₀ hz d hd hdeg] at hgam
    exact Int.mem_zmultiples_iff.mp hgam
  obtain ⟨k, hk⟩ := hmem
  rw [hn, hk, mul_comm]
  exact (Phi_Ushift d hd k s).symm

/-- Balls in the open right half plane are preconnected. -/
theorem isPreconnected_ball_subtype (t : ↥U) (ε : ℝ) :
    IsPreconnected (Metric.ball t ε : Set ↥U) := by
  have hset : (Metric.ball t ε : Set ↥U) = Subtype.val ⁻¹' Metric.ball (t : ℂ) ε := rfl
  rw [hset, isPreconnected_iff_preconnectedSpace]
  have hconv : Convex ℝ (U ∩ Metric.ball (t : ℂ) ε) :=
    U_convex.inter (convex_ball _ _)
  haveI : PreconnectedSpace ↥(U ∩ Metric.ball (t : ℂ) ε) :=
    isPreconnected_iff_preconnectedSpace.mp hconv.isPreconnected
  have ee : ↥(Subtype.val ⁻¹' (Metric.ball (t : ℂ) ε)) ≃ₜ ↥(U ∩ Metric.ball (t : ℂ) ε) :=
    { toFun := fun x => ⟨(x.1 : ℂ), x.1.2, x.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro z; ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h2 : IsPreconnected (univ : Set ↥(U ∩ Metric.ball (t : ℂ) ε)) := isPreconnected_univ
  have h3 := h2.image ⇑ee.symm ee.symm.continuous.continuousOn
  rw [Set.image_univ, Set.range_eq_univ.mpr ee.symm.surjective] at h3
  exact ⟨h3⟩

theorem Phi_continuous (d : ℕ) (hd : 0 < d) : Continuous (Phi d hd) :=
  u_continuous.comp (continuous_sigma d hd)

/-- The lift of the universal cover is an open map. -/
theorem isOpenMap_baseLift : IsOpenMap (baseLift hcov t₀ z₀ hz) := by
  intro V hV
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨t, htV, rfl⟩
  obtain ⟨e, hxe, heq⟩ := hcov.isLocalHomeomorph (baseLift hcov t₀ z₀ hz t)
  have hee : ∀ y : Z, q y = e y := fun y => congrFun heq y
  have hut : u t ∈ e.target := by
    rw [← baseLift_mem hcov t₀ z₀ hz t, hee (baseLift hcov t₀ z₀ hz t)]
    exact e.map_source hxe
  have hnhds : V ∩ u ⁻¹' e.target ∈ 𝓝 t :=
    Filter.inter_mem (hV.mem_nhds htV)
      (u_continuous.continuousAt (e.open_target.mem_nhds hut))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hpre : IsPreconnected (Metric.ball t ε : Set ↥U) := isPreconnected_ball_subtype t ε
  have hBV : Metric.ball t ε ⊆ V := fun s hs => (hsub hs).1
  have hBt : Metric.ball t ε ⊆ u ⁻¹' e.target := fun s hs => (hsub hs).2
  have hmemB : t ∈ Metric.ball t ε := Metric.mem_ball_self hε
  have heqon : (Metric.ball t ε).EqOn (fun s : ↥U => baseLift hcov t₀ z₀ hz s)
      (fun s : ↥U => e.symm (u s)) := by
    refine IsCoveringMap.eqOn_of_comp_eqOn hcov hpre
      (baseLift hcov t₀ z₀ hz).continuous.continuousOn
      (e.continuousOn_symm.comp u_continuous.continuousOn (fun s hs => hBt hs)) ?_ hmemB ?_
    · intro s hs
      simp only [Function.comp_apply]
      rw [baseLift_mem hcov t₀ z₀ hz s, hee, e.right_inv (hBt hs)]
    · rw [← e.left_inv hxe, ← hee, baseLift_mem hcov t₀ z₀ hz t]
  have hseteq : e.symm '' (u '' Metric.ball t ε) = e.source ∩ q ⁻¹' (u '' Metric.ball t ε) := by
    ext y; constructor
    · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨e.symm.map_source (hBt hs), ?_⟩
      show q (e.symm (u s)) ∈ u '' Metric.ball t ε
      rw [hee (e.symm (u s)), e.right_inv (hBt hs)]
      exact ⟨s, hs, rfl⟩
    · rintro ⟨hys, hy⟩
      obtain ⟨s, hs, hqs⟩ := hy
      exact ⟨u s, ⟨s, hs, rfl⟩, by rw [hqs, hee y, e.left_inv hys]⟩
  have hopen : IsOpen (e.symm '' (u '' Metric.ball t ε)) := by
    rw [hseteq]
    exact e.open_source.inter
      ((u_isCoveringMap.isOpenMap _ Metric.isOpen_ball).preimage hcov.continuous)
  have himg : baseLift hcov t₀ z₀ hz '' V ⊇ e.symm '' (u '' Metric.ball t ε) := by
    rintro y ⟨w, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hBV hs, heqon hs⟩
  have hmemB' : e.symm (u t) ∈ e.symm '' (u '' Metric.ball t ε) :=
    ⟨u t, ⟨t, hmemB, rfl⟩, rfl⟩
  have hzt : e.symm (u t) = baseLift hcov t₀ z₀ hz t := (heqon hmemB).symm
  rw [← hzt]
  exact Filter.mem_of_superset (hopen.mem_nhds hmemB') himg

theorem baseLift_surjective : Function.Surjective (baseLift hcov t₀ z₀ hz) := by
  intro v
  let γ : Path z₀ v := PathConnectedSpace.somePath z₀ v
  let α : C(unitInterval, ↥puncturedDisc) :=
    ⟨fun s => q (γ s), hcov.continuous.comp γ.continuous⟩
  have hα0 : α 0 = u t₀ := by
    show q (γ 0) = u t₀
    rw [γ.source, hz]
  let αt : C(unitInterval, ↥U) := u_isCoveringMap.liftPath α t₀ hα0
  have hαt_lift : ∀ s, u (αt s) = α s := fun s =>
    congrFun (u_isCoveringMap.liftPath_lifts α t₀ hα0) s
  have hαz : α 0 = q z₀ := by rw [hα0, hz]
  have hΓ₁ : (⟨fun s => baseLift hcov t₀ z₀ hz (αt s),
      (baseLift hcov t₀ z₀ hz).continuous.comp αt.continuous⟩ : C(unitInterval, Z)) =
      hcov.liftPath α z₀ hαz := by
    rw [hcov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · funext s
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [baseLift_mem hcov t₀ z₀ hz (αt s), hαt_lift s]
    · simp only [ContinuousMap.coe_mk]
      rw [show αt 0 = t₀ from u_isCoveringMap.liftPath_zero α t₀ hα0,
        baseLift_self hcov t₀ z₀ hz]
  have hΓ₂ : (γ.toContinuousMap : C(unitInterval, Z)) = hcov.liftPath α z₀ hαz := by
    rw [hcov.eq_liftPath_iff']
    exact ⟨by funext s; rfl, γ.source⟩
  refine ⟨αt 1, ?_⟩
  have h := congrFun (congrArg DFunLike.coe (hΓ₁.trans hΓ₂.symm)) 1
  simpa [γ.target] using h

/-- The covering isomorphism `Z ≃ 𝔻*`, defined on the lift `baseLift`. -/
noncomputable def psi (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (z : Z) : ↥puncturedDisc :=
  Phi d hd (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z)

theorem psi_base (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (t : ↥U) :
    psi hcov t₀ z₀ hz d hd hdeg (baseLift hcov t₀ z₀ hz t) = Phi d hd t := by
  refine Phi_well_def hcov t₀ z₀ hz d hd hdeg ?_
  exact Function.surjInv_eq (baseLift_surjective hcov t₀ z₀ hz) (baseLift hcov t₀ z₀ hz t)

theorem psi_pow (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (z : Z) :
    ((psi hcov t₀ z₀ hz d hd hdeg z : ↥puncturedDisc) : ℂ) ^ d =
      ((q z : ↥puncturedDisc) : ℂ) := by
  show ((Phi d hd (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z) :
      ↥puncturedDisc) : ℂ) ^ d = ((q z : ↥puncturedDisc) : ℂ)
  rw [Phi_pow]
  exact congrArg (fun x : ↥puncturedDisc => (x : ℂ))
    ((baseLift_mem hcov t₀ z₀ hz _).symm.trans
      (congrArg q (Function.surjInv_eq (baseLift_surjective hcov t₀ z₀ hz) z)))

theorem psi_injective (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) :
    Function.Injective (psi hcov t₀ z₀ hz d hd hdeg) := by
  intro z₁ z₂ h
  have h' : Phi d hd (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z₁) =
      Phi d hd (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z₂) := h
  obtain ⟨k, hk⟩ := (Phi_eq_iff d hd _ _).mp h'
  have hgam : (k * (d : ℤ)) ∈ Gamma hcov t₀ z₀ hz := by
    rw [Gamma_eq_zmultiples hcov t₀ z₀ hz d hd hdeg]
    exact Int.mem_zmultiples_iff.mpr ⟨k, mul_comm k (d : ℤ)⟩
  have hbl : baseLift hcov t₀ z₀ hz (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z₂) =
      baseLift hcov t₀ z₀ hz (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z₁) := by
    rw [hk]
    exact hgam _
  rw [Function.surjInv_eq (baseLift_surjective hcov t₀ z₀ hz) z₂,
    Function.surjInv_eq (baseLift_surjective hcov t₀ z₀ hz) z₁] at hbl
  exact hbl.symm

theorem psi_surjective (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) :
    Function.Surjective (psi hcov t₀ z₀ hz d hd hdeg) := by
  intro w
  obtain ⟨t, ht⟩ := Phi_surjective d hd w
  exact ⟨baseLift hcov t₀ z₀ hz t, by rw [psi_base hcov t₀ z₀ hz d hd hdeg t, ht]⟩

theorem psi_continuous (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) :
    Continuous (psi hcov t₀ z₀ hz d hd hdeg) := by
  rw [continuous_def]
  intro W hW
  have hpre : (psi hcov t₀ z₀ hz d hd hdeg) ⁻¹' W =
      baseLift hcov t₀ z₀ hz '' (Phi d hd ⁻¹' W) := by
    ext z; constructor
    · intro hzW
      refine ⟨Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z,
        show Phi d hd (Function.surjInv (baseLift_surjective hcov t₀ z₀ hz) z) ∈ W from hzW,
        Function.surjInv_eq (baseLift_surjective hcov t₀ z₀ hz) z⟩
    · rintro ⟨t, ht, rfl⟩
      show psi hcov t₀ z₀ hz d hd hdeg (baseLift hcov t₀ z₀ hz t) ∈ W
      rw [psi_base hcov t₀ z₀ hz d hd hdeg t]
      exact ht
  rw [hpre]
  exact isOpenMap_baseLift hcov t₀ z₀ hz _ (hW.preimage (Phi_continuous d hd))

/-- The inverse of `psi`, also defined through the lift. -/
noncomputable def psi' (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (w : ↥puncturedDisc) : Z :=
  Function.surjInv (psi_surjective hcov t₀ z₀ hz d hd hdeg) w

theorem psi_psi' (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (w : ↥puncturedDisc) :
    psi hcov t₀ z₀ hz d hd hdeg (psi' hcov t₀ z₀ hz d hd hdeg w) = w :=
  Function.surjInv_eq (f := psi hcov t₀ z₀ hz d hd hdeg)
    (psi_surjective hcov t₀ z₀ hz d hd hdeg) w

theorem psi'_psi (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (z : Z) :
    psi' hcov t₀ z₀ hz d hd hdeg (psi hcov t₀ z₀ hz d hd hdeg z) = z := by
  refine psi_injective hcov t₀ z₀ hz d hd hdeg ?_
  rw [psi_psi']

theorem psi'_base (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) (t : ↥U) :
    psi' hcov t₀ z₀ hz d hd hdeg (Phi d hd t) = baseLift hcov t₀ z₀ hz t := by
  rw [← psi_base hcov t₀ z₀ hz d hd hdeg t,
    psi'_psi hcov t₀ z₀ hz d hd hdeg]

theorem psi'_continuous (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ w : ↥puncturedDisc, (q ⁻¹' {w}).ncard = d) :
    Continuous (psi' hcov t₀ z₀ hz d hd hdeg) := by
  rw [continuous_def]
  intro T hT
  have hpre : (psi' hcov t₀ z₀ hz d hd hdeg) ⁻¹' T =
      Phi d hd '' (baseLift hcov t₀ z₀ hz ⁻¹' T) := by
    ext w; constructor
    · intro hw
      refine ⟨Function.surjInv (Phi_surjective d hd) w, ?_,
        Function.surjInv_eq (Phi_surjective d hd) w⟩
      show baseLift hcov t₀ z₀ hz (Function.surjInv (Phi_surjective d hd) w) ∈ T
      rw [← psi'_base hcov t₀ z₀ hz d hd hdeg,
        Function.surjInv_eq (Phi_surjective d hd) w]
      show psi' hcov t₀ z₀ hz d hd hdeg w ∈ T
      exact hw
    · rintro ⟨t, ht, rfl⟩
      show psi' hcov t₀ z₀ hz d hd hdeg (Phi d hd t) ∈ T
      rw [psi'_base hcov t₀ z₀ hz d hd hdeg t]
      exact ht
  rw [hpre]
  exact Phi_isOpenMap d hd _ (hT.preimage (baseLift hcov t₀ z₀ hz).continuous)

end Main

/-- **Classification of connected coverings of the punctured disc.**  A path connected
covering `q : Z → 𝔻*` all of whose fibres have `d ∈ ℕ>0` elements is isomorphic over `𝔻*` to
`z ↦ z ^ d`. -/
theorem exists_homeomorph_pow_of_isCoveringMap {Z : Type*} [TopologicalSpace Z]
    [PathConnectedSpace Z] {q : Z → ↥(Work.BasinSC.puncturedDisc)}
    (hcov : IsCoveringMap q)
    (hdeg : ∃ d : ℕ, 0 < d ∧ ∀ w : ↥(Work.BasinSC.puncturedDisc), (q ⁻¹' {w}).ncard = d) :
    ∃ (d : ℕ) (_ : 0 < d) (ψ : Z ≃ₜ ↥(Work.BasinSC.puncturedDisc)),
      ∀ z, ((ψ z : ℂ)) ^ d = ((q z : ↥(Work.BasinSC.puncturedDisc)) : ℂ) := by
  obtain ⟨d, hdpos, hd⟩ := hdeg
  have hne : (q ⁻¹' {u t0}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hd (u t0)]; exact hdpos.ne')
  obtain ⟨z₀, hz₀⟩ := hne
  have hz : q z₀ = u t0 := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz₀
  refine ⟨d, hdpos, ?_, ?_⟩
  · refine
      { toEquiv :=
          { toFun := psi hcov t0 z₀ hz d hdpos hd
            invFun := psi' hcov t0 z₀ hz d hdpos hd
            left_inv := psi'_psi hcov t0 z₀ hz d hdpos hd
            right_inv := psi_psi' hcov t0 z₀ hz d hdpos hd }
        continuous_toFun := psi_continuous hcov t0 z₀ hz d hdpos hd
        continuous_invFun := psi'_continuous hcov t0 z₀ hz d hdpos hd }
  · intro z
    exact psi_pow hcov t0 z₀ hz d hdpos hd z

end Work.BasinSC.CoverDisc
