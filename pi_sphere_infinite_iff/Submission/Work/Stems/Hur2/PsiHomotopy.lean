import Submission.Work.Stems.Hur2.PsiBased

/-!
# (Z): the filling of a based cube is homotopic to it

For a based `p : Ω^(Fin 2) X x₀` we exhibit the radial-expansion homotopy between `psiGenLoop x₀ p.1`
and `p`.  Writing `a := (t 0 : ℝ)`, `b := (t 1 : ℝ)`, `c s := (1 + s)/2` and
`xi u s := (2u - 1) * (1 - s/2) + 1/2` (a *polynomial* rescaling: `xi u 0 = 2u - 1/2`,
`xi u 1 = u`), the homotopy is

`H (s, t) := if sqRad t ≤ c s then p.1 (pair2 (clamp (xi a s)) (clamp (xi b s))) else x₀`.

At `s = 0` the inner condition is `t ∈ innerSet` (`sqRad_le_half_iff`) and the inner value is the
one defining `Ψ`, so `H (0, ·) = psiGenLoop x₀ p.1`; at `s = 1` the condition always holds and
`xi · 1 = id`, so `H (1, ·) = p.1`.  Each slice is `x₀` on `∂I²`.  Continuity is the pasting over
the two closed sets `A = {sqRad t ≤ c s}`, `B = {c s ≤ sqRad t}`: on `A` the first branch is a
composition of continuous maps, and on `B` the value is `x₀` — on the interface `sqRad t = c s` the
coordinate achieving the maximum has `|xi u s - 1/2| = c s · (1 - s/2) ≥ 1/2`, so it is clamped to
`0` or `1` and `p.1` is evaluated on `∂I²`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## The rescaling `xi` and its clamps -/

/-- The coercions of the endpoints of `I` (needed because `ring` treats them as atoms). -/
@[simp] theorem coe_zero_I : ((0 : unitInterval) : ℝ) = 0 := rfl

@[simp] theorem coe_one_I : ((1 : unitInterval) : ℝ) = 1 := rfl

/-- The radial rescaling of one coordinate at time `s`. -/
def xi (u : ℝ) (s : unitInterval) : ℝ := (2 * u - 1) * (1 - (s : ℝ) / 2) + 1/2

@[simp] theorem xi_zero (u : ℝ) : xi u 0 = 2 * u - 1/2 := by
  unfold xi; rw [coe_zero_I]; ring

@[simp] theorem xi_one (u : ℝ) : xi u 1 = u := by
  unfold xi; rw [coe_one_I]; ring

theorem abs_xi_sub_half (u : ℝ) (s : unitInterval) :
    |xi u s - 1/2| = |2 * u - 1| * (1 - (s : ℝ) / 2) := by
  have h : xi u s - 1/2 = (2 * u - 1) * (1 - (s : ℝ) / 2) := by unfold xi; ring
  rw [h, abs_mul, abs_of_nonneg (by linarith [(s : unitInterval).2.2] : (0:ℝ) ≤ 1 - (s:ℝ)/2)]

/-- The radius of the inner square at time `s`. -/
def cfun (s : unitInterval) : ℝ := (1 + (s : ℝ)) / 2

@[simp] theorem cfun_zero : cfun 0 = 1/2 := by unfold cfun; norm_num

@[simp] theorem cfun_one : cfun 1 = 1 := by unfold cfun; norm_num

theorem cfun_le_one (s : unitInterval) : cfun s ≤ 1 := by
  unfold cfun; linarith [s.2.2]

theorem le_cfun (s : unitInterval) : (1:ℝ)/2 ≤ cfun s := by
  unfold cfun; linarith [s.2.1]

/-! ## Continuity of the building blocks -/

theorem continuous_sqRad : Continuous sqRad := by
  show Continuous fun t : IC 2 => max |2 * (t 0 : ℝ) - 1| |2 * (t 1 : ℝ) - 1|
  exact (((continuous_const.mul (continuous_coord 0)).sub continuous_const).abs).max
    (((continuous_const.mul (continuous_coord 1)).sub continuous_const).abs)

theorem continuous_xi_pair (i : Fin 2) :
    Continuous fun z : unitInterval × IC 2 => xi (((z.2 i : unitInterval)) : ℝ) z.1 := by
  unfold xi
  fun_prop

/-- The rescaled point. -/
def radFun (s : unitInterval) (t : IC 2) : IC 2 :=
  pair2 (clamp (xi ((t 0 : unitInterval) : ℝ) s)) (clamp (xi ((t 1 : unitInterval) : ℝ) s))

theorem continuous_radFun : Continuous fun z : unitInterval × IC 2 => radFun z.1 z.2 := by
  show Continuous fun z : unitInterval × IC 2 =>
    pair2 (clamp (xi ((z.2 0 : unitInterval) : ℝ) z.1))
          (clamp (xi ((z.2 1 : unitInterval) : ℝ) z.1))
  exact continuous_pair2 (continuous_clamp.comp (continuous_xi_pair 0))
    (continuous_clamp.comp (continuous_xi_pair 1))

/-! ## The two closed regions and the homotopy -/

/-- The region where the first branch of the homotopy is used. -/
def A : Set (unitInterval × IC 2) := {z | sqRad z.2 ≤ cfun z.1}

/-- The complementary region. -/
def B : Set (unitInterval × IC 2) := {z | cfun z.1 ≤ sqRad z.2}

theorem isClosed_A : IsClosed A := by
  have h : A = {z : unitInterval × IC 2 | sqRad z.2 - (1 + (z.1:ℝ))/2 ≤ 0} := by
    ext z; simp only [A, cfun, Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rw [h]
  exact isClosed_le
    ((continuous_sqRad.comp continuous_snd).sub
      ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).div_const (2:ℝ)))
    continuous_const

theorem isClosed_B : IsClosed B := by
  have h : B = {z : unitInterval × IC 2 | (1 + (z.1:ℝ))/2 - sqRad z.2 ≤ 0} := by
    ext z; simp only [B, cfun, Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rw [h]
  exact isClosed_le
    (((continuous_const.add (continuous_subtype_val.comp continuous_fst)).div_const (2:ℝ)).sub
      (continuous_sqRad.comp continuous_snd))
    continuous_const

theorem univ_subset_A_union_B : (Set.univ : Set (unitInterval × IC 2)) ⊆ A ∪ B := by
  intro z _
  rcases le_total (sqRad z.2) (cfun z.1) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **The radial-expansion homotopy.** -/
def HomFun (x₀ : X) (p : GenLoop (Fin 2) X x₀) (z : unitInterval × IC 2) : X :=
  if sqRad z.2 ≤ cfun z.1 then p.1 (radFun z.1 z.2) else x₀

theorem HomFun_of_le {x₀ : X} {p : GenLoop (Fin 2) X x₀} {z : unitInterval × IC 2}
    (h : sqRad z.2 ≤ cfun z.1) : HomFun x₀ p z = p.1 (radFun z.1 z.2) := by
  rw [HomFun, if_pos h]

theorem HomFun_of_not_le {x₀ : X} {p : GenLoop (Fin 2) X x₀} {z : unitInterval × IC 2}
    (h : ¬ sqRad z.2 ≤ cfun z.1) : HomFun x₀ p z = x₀ := by
  rw [HomFun, if_neg h]

/-- **On the interface the clamped coordinate is `0` or `1`, so `p` is evaluated on `∂I²`.** -/
theorem HomFun_eq_x₀_of_mem_B (x₀ : X) (p : GenLoop (Fin 2) X x₀) {z : unitInterval × IC 2}
    (hz : z ∈ B) : HomFun x₀ p z = x₀ := by
  by_cases h : sqRad z.2 ≤ cfun z.1
  · rw [HomFun_of_le h]
    have heq : sqRad z.2 = cfun z.1 := le_antisymm h hz
    refine p.2 _ ?_
    rw [Cube.boundary]
    have key : ∀ i : Fin 2, |2 * (z.2 i : ℝ) - 1| = cfun z.1 →
        radFun z.1 z.2 i = 0 ∨ radFun z.1 z.2 i = 1 := by
      intro i hi
      have hge : (1:ℝ)/2 ≤ |xi (((z.2 i : unitInterval)) : ℝ) z.1 - 1/2| := by
        rw [abs_xi_sub_half, hi]
        unfold cfun
        have hs0 : (0:ℝ) ≤ (z.1 : ℝ) := z.1.2.1
        have hs1 : (z.1 : ℝ) ≤ 1 := z.1.2.2
        nlinarith
      have hxi : clamp (xi (((z.2 i : unitInterval)) : ℝ) z.1) = 0 ∨
          clamp (xi (((z.2 i : unitInterval)) : ℝ) z.1) = 1 := by
        rcases le_total ((1:ℝ)/2) (xi (((z.2 i : unitInterval)) : ℝ) z.1) with hgt | hlt
        · right
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ xi _ _ - 1/2)] at hge
          exact clamp_of_ge_one (by linarith : (1:ℝ) ≤ xi _ _)
        · left
          rw [abs_of_nonpos (by linarith : xi _ _ - 1/2 ≤ 0)] at hge
          exact clamp_of_le_zero (by linarith : xi _ _ ≤ 0)
      have hpair : radFun z.1 z.2 i = clamp (xi (((z.2 i : unitInterval)) : ℝ) z.1) := by
        rw [radFun]
        by_cases hi0 : i = 0
        · subst hi0; rw [pair2_zero]
        · have hi1 : i = 1 := by fin_cases i <;> simp_all
          subst hi1; rw [pair2_one]
      rcases hxi with hxi | hxi
      · exact Or.inl (by rw [hpair, hxi])
      · exact Or.inr (by rw [hpair, hxi])
    rcases max_cases |2 * (z.2 0 : ℝ) - 1| |2 * (z.2 1 : ℝ) - 1| with ⟨hm, _⟩ | ⟨hm, _⟩
    · refine ⟨0, ?_⟩
      have h0 : |2 * (z.2 0 : ℝ) - 1| = cfun z.1 := by rw [← hm]; exact heq
      exact key 0 h0
    · refine ⟨1, ?_⟩
      have h1 : |2 * (z.2 1 : ℝ) - 1| = cfun z.1 := by rw [← hm]; exact heq
      exact key 1 h1
  · rw [HomFun_of_not_le h]

theorem continuousOn_HomFun_A (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    ContinuousOn (HomFun x₀ p) A :=
  (p.1.continuous.comp continuous_radFun).continuousOn.congr
    (fun z hz => HomFun_of_le hz)

theorem continuousOn_HomFun_B (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    ContinuousOn (HomFun x₀ p) B :=
  continuous_const.continuousOn.congr (fun z hz => HomFun_eq_x₀_of_mem_B x₀ p hz)

theorem continuous_HomFun (x₀ : X) (p : GenLoop (Fin 2) X x₀) : Continuous (HomFun x₀ p) := by
  have huniv : (Set.univ : Set (unitInterval × IC 2)) = A ∪ B :=
    (Set.eq_univ_iff_forall.mpr (fun z => univ_subset_A_union_B (Set.mem_univ z))).symm
  rw [← continuousOn_univ, huniv, continuousOn_union_iff_of_isClosed isClosed_A isClosed_B]
  exact ⟨continuousOn_HomFun_A x₀ p, continuousOn_HomFun_B x₀ p⟩

/-! ## The endpoints -/

theorem sqRad_le_one (t : IC 2) : sqRad t ≤ 1 := by
  have h0 : (0:ℝ) ≤ (t 0 : ℝ) := (t 0).2.1
  have h1 : (t 0 : ℝ) ≤ 1 := (t 0).2.2
  have h2 : (0:ℝ) ≤ (t 1 : ℝ) := (t 1).2.1
  have h3 : (t 1 : ℝ) ≤ 1 := (t 1).2.2
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith

theorem radFun_one (t : IC 2) : radFun 1 t = t := by
  rw [radFun, xi_one, xi_one]
  have ha : clamp ((t 0 : unitInterval) : ℝ) = t 0 :=
    clamp_of_mem ⟨(t 0).2.1, (t 0).2.2⟩
  have hb : clamp ((t 1 : unitInterval) : ℝ) = t 1 :=
    clamp_of_mem ⟨(t 1).2.1, (t 1).2.2⟩
  rw [ha, hb]
  funext i
  fin_cases i <;> simp [pair2]

theorem HomFun_zero (x₀ : X) (p : GenLoop (Fin 2) X x₀) (t : IC 2) :
    HomFun x₀ p (0, t) = psiFun x₀ p.1 t := by
  by_cases h : sqRad t ≤ 1/2
  · have hi : t ∈ innerSet := (sqRad_le_half_iff t).mp h
    rw [HomFun_of_le (by rw [cfun_zero]; exact h), psiFun_apply_of_mem_inner p hi]
    congr 1
    rw [radFun, xi_zero, xi_zero]
  · have hni : t ∉ innerSet := fun hc => h ((sqRad_le_half_iff t).mpr hc)
    rw [HomFun_of_not_le (by rw [cfun_zero]; exact h), psiFun_apply_of_not_mem_inner p hni]

theorem HomFun_one (x₀ : X) (p : GenLoop (Fin 2) X x₀) (t : IC 2) :
    HomFun x₀ p (1, t) = p.1 t := by
  rw [HomFun_of_le (by rw [cfun_one]; exact sqRad_le_one t), radFun_one]

/-- Each slice of the homotopy is constant `x₀` on the boundary of the square. -/
theorem HomFun_boundary (x₀ : X) (p : GenLoop (Fin 2) X x₀) (s : unitInterval) {t : IC 2}
    (ht : t ∈ Cube.boundary (Fin 2)) : HomFun x₀ p (s, t) = x₀ :=
  HomFun_eq_x₀_of_mem_B x₀ p (by
    change cfun s ≤ sqRad t
    rw [sqRad_eq_one_of_mem_boundary ht]
    exact cfun_le_one s)

/-! ## (Z) -/

/-- **(Z)**: the filling of a based 2-cube is homotopic to it, relative to the boundary. -/
theorem psiGenLoop_homotopic (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    GenLoop.Homotopic (psiGenLoop x₀ p.1) p :=
  ⟨{ toFun := fun z => HomFun x₀ p z
     continuous_toFun := continuous_HomFun x₀ p
     map_zero_left := fun t => HomFun_zero x₀ p t
     map_one_left := fun t => HomFun_one x₀ p t
     prop' := fun s => fun t ht => by
       have hni : t ∉ innerSet := by
         intro hc
         have h1 : sqRad t = 1 := sqRad_eq_one_of_mem_boundary ht
         have h2 : sqRad t ≤ 1/2 := (sqRad_le_half_iff t).mpr hc
         linarith
       show HomFun x₀ p (s, t) = psiFun x₀ p.1 t
       rw [HomFun_boundary x₀ p s ht, psiFun_apply_of_not_mem_inner p hni] }⟩

/-- **(Z), symmetric form**: a based 2-cube is homotopic to its filling, relative to the boundary.
This is the form used downstream: `⟦p⟧ = ⟦Ψ p⟧`, hence `[p] = Ψ(p)`. -/
theorem homotopic_psiGenLoop (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    GenLoop.Homotopic p (psiGenLoop x₀ p.1) :=
  (psiGenLoop_homotopic x₀ p).symm

end

end Work.Stems.Hur2
