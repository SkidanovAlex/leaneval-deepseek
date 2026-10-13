import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.nullDimLE_mono_dim

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory

namespace Work.WilE7.Endgame

/-- Coordinate pullback of a Lebesgue-null set.  If `f : Fin m → Fin n` is injective and
`A ⊆ ℝ^m` has measure zero, then the set of `w : ℝ^n` whose restriction to the coordinates hit by
`f` lies in `A` has measure zero.

The restriction map `w ↦ w ∘ f` is the surjective linear map `LinearMap.funLeft ℝ ℝ f`
(`LinearMap.funLeft_surjective_of_injective`), and a surjective linear map pulls null sets back to
null sets (`volume_preimage_null_of_surjective_linear`). -/
theorem volume_comp_setOf_null {n m : ℕ} {f : Fin m → Fin n}
    (hf : Function.Injective f) {A : Set (Fin m → ℝ)} (hA : volume A = 0) :
    volume {w : Fin n → ℝ | w ∘ f ∈ A} = 0 := by
  let ρ : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := LinearMap.funLeft ℝ ℝ f
  have hpre : {w : Fin n → ℝ | w ∘ f ∈ A} = ρ ⁻¹' A := rfl
  rw [hpre]
  exact Work.WilE7.DimAPI.volume_preimage_null_of_surjective_linear ρ
    ((LinearMap.funLeft_surjective_of_injective (R := ℝ) (M := ℝ) f hf)) hA

theorem nullDimLE_finInit {N K : ℕ} {X : Set (Fin N → ℝ)}
    (h : Work.WilE7.MainDesign.NullDimLE X K) :
    Work.WilE7.MainDesign.NullDimLE {z : Fin (N + 1) → ℝ | Fin.init z ∈ X} (K + 1) := by
  intro e
  by_cases hlast : Fin.last N ∈ Set.range e
  · -- Some coordinate of `e` is the last coordinate: the free coordinate is projected away.
    obtain ⟨i₀, hi₀⟩ := hlast
    have hval : ∀ t : Fin (K + 1), (e (Fin.succAbove i₀ t)).val < N := by
      intro t
      by_contra hlt
      have hlt' : (e (Fin.succAbove i₀ t)).val = N := by
        have := (e (Fin.succAbove i₀ t)).isLt
        omega
      have heq : e (Fin.succAbove i₀ t) = Fin.last N :=
        Fin.ext (by rw [hlt', Fin.val_last])
      exact Fin.succAbove_ne i₀ t (e.injective (heq.trans hi₀.symm))
    let e' : Fin (K + 1) ↪ Fin N :=
      ⟨fun t => ⟨(e (Fin.succAbove i₀ t)).val, hval t⟩, by
        intro a b hab
        have h2 : (e (Fin.succAbove i₀ a)).val = (e (Fin.succAbove i₀ b)).val :=
          congrArg (fun x : Fin N => x.val) hab
        exact Fin.succAbove_right_injective (e.injective (Fin.ext h2))⟩
    have hnull : volume {w : Fin (K + 1 + 1) → ℝ |
        w ∘ (Fin.succAbove i₀ : Fin (K + 1) → Fin (K + 1 + 1)) ∈
          (fun x : Fin N → ℝ => x ∘ (e' : Fin (K + 1) → Fin N)) '' X} = 0 :=
      volume_comp_setOf_null (f := (Fin.succAbove i₀ : Fin (K + 1) → Fin (K + 1 + 1)))
        Fin.succAbove_right_injective (h e')
    refine measure_mono_null ?_ hnull
    rintro w ⟨z, hz, rfl⟩
    refine ⟨Fin.init z, hz, ?_⟩
    funext t
    show Fin.init z (e' t) = z (e (Fin.succAbove i₀ t))
    rw [show Fin.init z (e' t) = z ((e' t).castSucc) from rfl]
    exact congrArg z (Fin.ext rfl)
  · -- No coordinate of `e` is the last one: `e` is an embedding of the first `N` coordinates,
    -- and the dimension bound for `X` is raised by one.
    have hval : ∀ i : Fin (K + 1 + 1), (e i).val < N := by
      intro i
      by_contra hlt
      have hlt' : (e i).val = N := by
        have := (e i).isLt
        omega
      exact hlast ⟨i, Fin.ext (by rw [hlt', Fin.val_last])⟩
    let e' : Fin (K + 1 + 1) ↪ Fin N :=
      ⟨fun i => ⟨(e i).val, hval i⟩, by
        intro a b hab
        have h2 : (e a).val = (e b).val := congrArg (fun x : Fin N => x.val) hab
        exact e.injective (Fin.ext h2)⟩
    have hsub : (fun z : Fin (N + 1) → ℝ => z ∘ e) '' {z : Fin (N + 1) → ℝ | Fin.init z ∈ X} ⊆
        (fun x : Fin N → ℝ => x ∘ (e' : Fin (K + 1 + 1) → Fin N)) '' X := by
      rintro w ⟨z, hz, rfl⟩
      refine ⟨Fin.init z, hz, ?_⟩
      funext i
      show Fin.init z (e' i) = z (e i)
      rw [show Fin.init z (e' i) = z ((e' i).castSucc) from rfl]
      exact congrArg z (Fin.ext rfl)
    exact measure_mono_null hsub
      (Work.WilE7.DimAPI.nullDimLE_mono_dim h (Nat.le_succ K) e')

end Work.WilE7.Endgame
