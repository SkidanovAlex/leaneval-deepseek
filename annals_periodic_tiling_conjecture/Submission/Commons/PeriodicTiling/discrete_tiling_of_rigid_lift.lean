import Mathlib
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift

namespace Commons.PeriodicTiling

open Filter Bornology MeasureTheory
open scoped Pointwise

set_option autoImplicit false

lemma IsContinuousTiling.eq_of_mem_of_mem_of_measure_pos
    {d : ℕ} {S Λ : Set (Fin d → ℝ)} (h : IsContinuousTiling S Λ)
    {v w : Fin d → ℝ} (hv : v ∈ Λ) (hw : w ∈ Λ)
    (hpos : 0 < volume {x : Fin d → ℝ | x ∈ v +ᵥ S ∧ x ∈ w +ᵥ S}) :
    v = w := by
  by_contra hne
  have hbad : volume {x : Fin d → ℝ | ¬ ∃! u ∈ Λ, x ∈ u +ᵥ S} = 0 := by
    exact (ae_iff (μ := volume)).1 h
  have hsub : {x : Fin d → ℝ | x ∈ v +ᵥ S ∧ x ∈ w +ᵥ S} ⊆
      {x : Fin d → ℝ | ¬ ∃! u ∈ Λ, x ∈ u +ᵥ S} := by
    intro x hx huniq
    have hvx : v ∈ Λ ∧ x ∈ v +ᵥ S := ⟨hv, hx.1⟩
    have hwx : w ∈ Λ ∧ x ∈ w +ᵥ S := ⟨hw, hx.2⟩
    exact hne (ExistsUnique.unique huniq hvx hwx)
  have hle : volume {x : Fin d → ℝ | x ∈ v +ᵥ S ∧ x ∈ w +ᵥ S} ≤
      volume {x : Fin d → ℝ | ¬ ∃! u ∈ Λ, x ∈ u +ᵥ S} := measure_mono hsub
  rw [hbad] at hle
  exact (not_lt_of_ge hle) hpos

theorem discrete_tiling_of_rigid_lift
    {d : ℕ} {R : Set (Fin d → ℝ)}
    {F : Set (Fin d → ℤ)} (hFne : F.Nonempty)
    {Λ : Set (Fin d → ℝ)} {t : Fin d → ℝ}
    (hRp : 0 < volume R)
    (hΛtile : IsContinuousTiling (((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F) + R) Λ)
    (hEq : Λ + (fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F =
      (fun x : Fin d → ℝ => x + t) ''
        {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}) :
    IsTiling F {z : Fin d → ℤ |
      (fun i : Fin d => (z i : ℝ)) ∈ Λ - ({t} : Set (Fin d → ℝ))} := by
  classical
  have _ : F.Nonempty := hFne
  let emb : (Fin d → ℤ) →+ (Fin d → ℝ) :=
  { toFun := fun z => fun i => (z i : ℝ)
    map_zero' := by
      ext i
      simp
    map_add' := by
      intro z w
      ext i
      simp [Pi.add_apply, Int.cast_add] }
  let E : Set (Fin d → ℝ) := emb '' F
  let Z : Set (Fin d → ℝ) := {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}
  let A : Set (Fin d → ℤ) := {z | emb z ∈ Λ - ({t} : Set (Fin d → ℝ))}
  have hΛtile' : IsContinuousTiling (E + R) Λ := by
    simpa [E, emb] using hΛtile
  have hEq' : Λ + E = (fun x : Fin d → ℝ => x + t) '' Z := by
    simpa [E, Z, emb] using hEq
  have hemb_inj : Function.Injective emb := by
    intro z w h
    ext i
    have h' : (z i : ℝ) = (w i : ℝ) := congr_fun h i
    exact Int.cast_injective h'
  change IsTiling F A
  rw [IsTiling]
  change AddSubgroup.IsComplement A F
  dsimp [AddSubgroup.IsComplement]
  constructor
  · -- injectivity
    rintro ⟨⟨a, haA⟩, ⟨f, hfF⟩⟩ ⟨⟨a', haA'⟩, ⟨f', hfF'⟩⟩ hsum
    have hsumV : emb a + emb f = emb a' + emb f' := by
      simpa [map_add] using congrArg emb hsum
    have hlam_mem : emb a + t ∈ Λ := by
      rcases Set.mem_sub.mp haA with ⟨lam, hlamΛ, y, hyt, hlam_sub⟩
      have hyt' : y = t := Set.mem_singleton_iff.mp hyt
      rw [hyt'] at hlam_sub
      have hlam_eq : lam = emb a + t := by
        exact sub_eq_iff_eq_add.mp hlam_sub
      simpa [hlam_eq] using hlamΛ
    have hlam'_mem : emb a' + t ∈ Λ := by
      rcases Set.mem_sub.mp haA' with ⟨lam', hlam'Λ, y, hyt, hlam'_sub⟩
      have hyt' : y = t := Set.mem_singleton_iff.mp hyt
      rw [hyt'] at hlam'_sub
      have hlam'_eq : lam' = emb a' + t := by
        exact sub_eq_iff_eq_add.mp hlam'_sub
      simpa [hlam'_eq] using hlam'Λ
    have hlam_sum : (emb a + t) + emb f = (emb a' + t) + emb f' := by
      calc
        (emb a + t) + emb f = emb a + emb f + t := by abel
        _ = emb a' + emb f' + t := by rw [hsumV]
        _ = (emb a' + t) + emb f' := by abel
    have hsubset : (fun r : Fin d → ℝ => (emb a + t) + (emb f + r)) '' R ⊆
        {x : Fin d → ℝ | x ∈ (emb a + t) +ᵥ (E + R) ∧ x ∈ (emb a' + t) +ᵥ (E + R)} := by
      intro x hx
      rcases hx with ⟨r, hrR, rfl⟩
      constructor
      · refine Set.mem_vadd_set.mpr ⟨emb f + r, ?_, ?_⟩
        · exact Set.add_mem_add ⟨f, hfF, rfl⟩ hrR
        · rw [vadd_eq_add]
      · have hxeq : (emb a + t) + (emb f + r) =
            (emb a' + t) + (emb f' + r) := by
          calc
            (emb a + t) + (emb f + r) = ((emb a + t) + emb f) + r := by abel
            _ = ((emb a' + t) + emb f') + r := by rw [hlam_sum]
            _ = (emb a' + t) + (emb f' + r) := by abel
        change (emb a + t) + (emb f + r) ∈ (emb a' + t) +ᵥ (E + R)
        rw [hxeq]
        refine Set.mem_vadd_set.mpr ⟨emb f' + r, ?_, ?_⟩
        · exact Set.add_mem_add ⟨f', hfF', rfl⟩ hrR
        · rw [vadd_eq_add]
    have hpos_sub : 0 < volume ((fun r : Fin d → ℝ => (emb a + t) + (emb f + r)) '' R) := by
      have hfun : (fun r : Fin d → ℝ => (emb a + t) + (emb f + r)) =
          (fun r : Fin d → ℝ => ((emb a + t) + emb f) + r) := by
        funext r
        abel
      rw [hfun, Set.image_add_left]
      simp [measure_preimage_add]
      exact hRp
    have hpos_inter : 0 < volume {x : Fin d → ℝ | x ∈ (emb a + t) +ᵥ (E + R) ∧
        x ∈ (emb a' + t) +ᵥ (E + R)} := by
      exact lt_of_lt_of_le hpos_sub (measure_mono hsubset)
    have hlam_eq : emb a + t = emb a' + t := by
      exact IsContinuousTiling.eq_of_mem_of_mem_of_measure_pos hΛtile' hlam_mem hlam'_mem hpos_inter
    have hembf : emb f = emb f' := by
      apply add_left_cancel (a := emb a + t)
      simpa [hlam_eq] using hlam_sum
    have hf_eq : f = f' := hemb_inj hembf
    have ha_eq : a = a' := by
      apply add_right_cancel (b := f)
      simpa [hf_eq] using hsum
    apply Prod.ext
    · apply Subtype.ext
      exact ha_eq
    · apply Subtype.ext
      exact hf_eq
  · -- surjectivity
    intro g
    have hgZ : emb g ∈ Z := by
      refine ⟨g, ?_⟩
      intro i
      rfl
    have hg_mem_rhs : emb g + t ∈ (fun x : Fin d → ℝ => x + t) '' Z := by
      refine ⟨emb g, hgZ, rfl⟩
    have hg_mem_LE : emb g + t ∈ Λ + E := by
      simpa [hEq'] using hg_mem_rhs
    rcases Set.mem_add.mp hg_mem_LE with ⟨lam, hlamΛ, e, heE, hlam_e⟩
    rcases (Set.mem_image (f := emb) (s := F) (y := e)).mp heE with ⟨f, hfF, hef⟩
    have hlam_e' : lam + emb f = emb g + t := by
      simpa [hef] using hlam_e
    have hsub : lam - t = emb (g - f) := by
      calc
        lam - t = emb g + t - emb f - t := by
          rw [← hlam_e']
          abel
        _ = emb g - emb f := by abel
        _ = emb (g - f) := by rw [map_sub]
    have haA : g - f ∈ A := by
      dsimp [A]
      rw [← hsub]
      exact Set.sub_mem_sub hlamΛ (by simp)
    refine ⟨((⟨g - f, haA⟩, ⟨f, hfF⟩) : A × F), ?_⟩
    change (g - f) + f = g
    exact sub_add_cancel g f

end Commons.PeriodicTiling
