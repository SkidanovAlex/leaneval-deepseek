import Submission.Work.Serre.MapPathDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The mapping path space is a Serre fibration

`mpathQ p = (e, γ) ↦ γ 1` is the projection of the mapping path space of `p`;
it is a Hurewicz fibration (hence a Serre fibration) for *every* continuous map `p`, with the
explicit lift obtained by concatenating the path of the given lift with the tail of the homotopy.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **`mpathQ p` has the homotopy lifting property with respect to every space `Z`** (it is a
Hurewicz fibration).

Given a lift `f : Z → mpath p` of `mpathQ p ∘ f = H (·, 0)` and a homotopy `H` in `B`, the lift is
`H' (t, z) = (e z, γ_z * s ↦ H (t s, z))`: the `E`-coordinate is unchanged (the path of `f z`
always starts at `p (e z)`), and the path is the concatenation of `γ_z` with the tail `H (t ·, z)`,
reparametrised so that the junction is at `s = 1 - t/2`. -/
theorem mpathQ_hasHLP (p : C(E, B)) (Z : Type) [TopologicalSpace Z] :
    Work.StemsB.HasHLP (mpathQ p) Z := by
  intro f b H
  have hQ : ∀ z : Z, mpathQ p (f z) = (mpathSnd p (f z)) 1 := fun z => rfl
  have hF : Continuous fun q : Z × I => (mpathSnd p (f q.1)) q.2 :=
    continuous_eval.comp
      (((mpathSnd p).continuous.comp (f.continuous.comp continuous_fst)).prodMk continuous_snd)
  let A : (I × Z) × I → B := fun x =>
    (mpathSnd p (f x.1.2)) (Work.StemsB.clampI ((x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2)))
  have hA : Continuous A := by
    show Continuous fun x : (I × Z) × I =>
      (mpathSnd p (f x.1.2)) (Work.StemsB.clampI ((x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2)))
    exact hF.comp (Continuous.prodMk (continuous_snd.comp continuous_fst)
      (Work.StemsB.continuous_clampI.comp (Continuous.div (by fun_prop) (by fun_prop) (fun x => by
        have h := x.1.1.2.2; linarith))))
  let Bc : (I × Z) × I → B := fun x =>
    H.toContinuousMap (Work.StemsB.clampI (2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ)), x.1.2)
  have hBc : Continuous Bc := by
    show Continuous fun x : (I × Z) × I =>
      H.toContinuousMap (Work.StemsB.clampI (2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ)), x.1.2)
    exact H.toContinuousMap.continuous.comp (Continuous.prodMk
      (Work.StemsB.continuous_clampI.comp (by fun_prop)) (continuous_snd.comp continuous_fst))
  have hagree : ∀ x : (I × Z) × I, (x.2 : ℝ) = 1 - (x.1.1 : ℝ) / 2 → A x = Bc x := by
    intro x hx
    show (mpathSnd p (f x.1.2)) (Work.StemsB.clampI ((x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2)))
      = H.toContinuousMap (Work.StemsB.clampI (2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ)), x.1.2)
    have hne : (1 : ℝ) - (x.1.1 : ℝ) / 2 ≠ 0 := by have h := x.1.1.2.2; linarith
    have h1 : (x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2) = 1 := by rw [hx, div_self hne]
    have h2 : 2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ) = 0 := by rw [hx]; ring
    rw [h1, h2, Work.StemsB.clampI_one, Work.StemsB.clampI_zero]
    have key := (H.map_zero_left x.1.2).symm
    simp only [ContinuousMap.comp_apply] at key
    rw [← hQ x.1.2]
    exact key
  let Ψ : (I × Z) × I → B := fun x => if (x.2 : ℝ) ≤ 1 - (x.1.1 : ℝ) / 2 then A x else Bc x
  have hΨ : Continuous Ψ := by
    show Continuous fun x : (I × Z) × I =>
      if (x.2 : ℝ) ≤ 1 - (x.1.1 : ℝ) / 2 then A x else Bc x
    exact Continuous.if_le hA hBc (by fun_prop) (by fun_prop) hagree
  let Ψcm : C((I × Z) × I, B) := ⟨Ψ, hΨ⟩
  let cur : C(I × Z, C(I, B)) := Ψcm.curry
  have hcur : ∀ (y : I × Z) (s : I), cur y s = Ψ (y, s) := fun y s =>
    ContinuousMap.curry_apply Ψcm y s
  have hbase : ∀ y : I × Z, cur y 0 = p (f y.2).1.1 := by
    intro y
    rw [hcur y 0]
    show (if (((0 : I)) : ℝ) ≤ 1 - (y.1 : ℝ) / 2 then A (y, 0) else Bc (y, 0))
      = p (f y.2).1.1
    have h0I : (((0 : I)) : ℝ) = 0 := rfl
    have hcon : (((0 : I)) : ℝ) ≤ 1 - (y.1 : ℝ) / 2 := by
      rw [h0I]; have := y.1.2.2; linarith
    rw [if_pos hcon]
    show (mpathSnd p (f y.2)) (Work.StemsB.clampI ((((0 : I)) : ℝ) / (1 - (y.1 : ℝ) / 2)))
      = p (f y.2).1.1
    have hz : (((0 : I)) : ℝ) / (1 - (y.1 : ℝ) / 2) = 0 := by rw [h0I, zero_div]
    rw [hz, Work.StemsB.clampI_zero]
    exact (f y.2).2
  let H' : C(I × Z, mpath p) :=
    ⟨fun y => ⟨((f y.2).1.1, cur y), hbase y⟩, by
      refine Continuous.subtype_mk (Continuous.prodMk ?_ cur.continuous) _
      exact ((mpathFst p).comp f).continuous.comp continuous_snd⟩
  have hH'val : ∀ y : I × Z, H' y = ⟨((f y.2).1.1, cur y), hbase y⟩ := fun y => rfl
  have hH'0 : ∀ z : Z, H' (0, z) = f z := by
    intro z
    rw [hH'val (0, z)]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      rw [hcur (0, z) s]
      show (if (s : ℝ) ≤ 1 - (((0 : I)) : ℝ) / 2 then A ((0, z), s) else Bc ((0, z), s))
        = (f z).1.2 s
      have h0I : (((0 : I)) : ℝ) = 0 := rfl
      have hcon : (s : ℝ) ≤ 1 - (((0 : I)) : ℝ) / 2 := by
        rw [h0I]; have := s.2.2; linarith
      rw [if_pos hcon]
      show (mpathSnd p (f z)) (Work.StemsB.clampI ((s : ℝ) / (1 - 0 / 2))) = (f z).1.2 s
      rw [zero_div, sub_zero, div_one, Work.StemsB.clampI_coe_I]
      rfl
  have hH'1 : ∀ z : Z, H' (1, z) = ⟨((f z).1.1, cur (1, z)), hbase (1, z)⟩ := fun z => rfl
  let g : C(Z, mpath p) := ⟨fun z => H' (1, z),
    H'.continuous.comp (Continuous.prodMk continuous_const continuous_id)⟩
  have g_apply : ∀ z : Z, g z = H' (1, z) := fun z => rfl
  refine ⟨g, ?_, ?_⟩
  · exact ⟨H', hH'0, fun z => by rw [g_apply z, hH'1 z]⟩
  · apply ContinuousMap.ext
    rintro ⟨t, z⟩
    show cur (t, z) 1 = H.toContinuousMap (t, z)
    rw [hcur (t, z) 1]
    show (if (((1 : I)) : ℝ) ≤ 1 - (t : ℝ) / 2 then A ((t, z), 1) else Bc ((t, z), 1))
      = H.toContinuousMap (t, z)
    have h1I : (((1 : I)) : ℝ) = 1 := rfl
    by_cases h : (((1 : I)) : ℝ) ≤ 1 - (t : ℝ) / 2
    · rw [if_pos h]
      have ht : (t : ℝ) = 0 := by have := t.2.1; linarith
      have hte : t = 0 := Subtype.ext ht
      subst hte
      show (mpathSnd p (f z)) (Work.StemsB.clampI (1 / (1 - (((0 : I)) : ℝ) / 2)))
        = H.toContinuousMap (0, z)
      have hnum : (1 : ℝ) / (1 - (((0 : I)) : ℝ) / 2) = 1 := by
        have h0I : (((0 : I)) : ℝ) = 0 := rfl
        rw [h0I]; norm_num
      rw [hnum, Work.StemsB.clampI_one]
      have key := (H.map_zero_left z).symm
      simp only [ContinuousMap.comp_apply] at key
      rw [← hQ z]
      exact key
    · rw [if_neg h]
      show H.toContinuousMap (Work.StemsB.clampI (2 * (((1 : I)) : ℝ) - 2 + (t : ℝ)), z)
        = H.toContinuousMap (t, z)
      have key : 2 * (((1 : I)) : ℝ) - 2 + (t : ℝ) = (t : ℝ) := by rw [h1I]; ring
      rw [key, Work.StemsB.clampI_coe_I]


/-- **`mpathQ p` is a Serre fibration**, for every continuous map `p`. -/
theorem mpathQ_isSerreFibration (p : C(E, B)) :
    Work.StemsB.IsSerreFibration (mpathQ p) :=
  fun n => mpathQ_hasHLP p (Fin n → I)

end

end Work.Serre
