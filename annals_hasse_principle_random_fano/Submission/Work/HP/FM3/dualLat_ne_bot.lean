import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.FM3.basic

/-!
# A discrete lattice has a nonzero dual

If `K ⊆ ℝ^ι` is a discrete `ℤ`-submodule of real rank at least one, then `dualLat K` is nonzero:
a `ℤ`-basis of `K` (available since `K` is a lattice) admits a dual vector, which pairs
integrally with all of `K`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem dualLat_ne_bot_of_discrete (K : Submodule ℤ (ι → ℝ))
    (h : DiscreteTopology ↥K) (hrk : 1 ≤ rkR K) :
    ∃ y ∈ dualLat K, y ≠ 0 := by
  letI := h
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := ↥K)
  have hcard : Module.finrank ℤ ↥K = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hrkK : rkR K = n := (rank_finrank_discrete K h).symm.trans hcard
  have hn1 : 0 < n := by have h1 := hrk; rw [hrkK] at h1; omega
  -- the `ℤ`-basis spans `K` over `ℤ`
  have hspanK : ∀ z : ↥K, ∃ c : Fin n → ℤ, ∑ j, c j • b j = z := by
    intro z
    have hz : z ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hz
  have hspanZ : Submodule.span ℤ (Set.range fun j => ((b j : ↥K) : ι → ℝ)) = K := by
    have h1 : Set.range (fun j => ((b j : ↥K) : ι → ℝ))
        = (Submodule.subtype K) '' Set.range b := by
      rw [← Set.range_comp (Submodule.subtype K) b, Function.comp_def, Submodule.coe_subtype]
    rw [h1, ← Submodule.map_span (f := Submodule.subtype K) (s := Set.range b), b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hspanV : Submodule.span ℝ (K : Set (ι → ℝ))
      = Submodule.span ℝ (Set.range fun j => ((b j : ↥K) : ι → ℝ)) := by
    refine le_antisymm ?_ (Submodule.span_mono ?_)
    · rw [Submodule.span_le]
      intro x hx
      have hx' : x ∈ Submodule.span ℤ (Set.range fun j => ((b j : ↥K) : ι → ℝ)) := by
        rw [hspanZ]; exact hx
      have hle : ∀ x ∈ Submodule.span ℤ (Set.range fun j => ((b j : ↥K) : ι → ℝ)),
          x ∈ Submodule.span ℝ (Set.range fun j => ((b j : ↥K) : ι → ℝ)) := by
        intro x hx''
        refine Submodule.span_induction
          (p := fun y _ => y ∈ Submodule.span ℝ (Set.range fun j => ((b j : ↥K) : ι → ℝ)))
          ?_ ?_ ?_ ?_ hx''
        · rintro y ⟨j, rfl⟩; exact Submodule.subset_span ⟨j, rfl⟩
        · exact Submodule.zero_mem _
        · intro a c _ _ ha hc; exact Submodule.add_mem _ ha hc
        · intro m a _ ha
          rw [← Int.cast_smul_eq_zsmul ℝ m a]
          exact Submodule.smul_mem _ _ ha
      exact hle x hx'
    · rintro z ⟨j, rfl⟩
      exact (b j).2
  let V : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (K : Set (ι → ℝ))
  let Ψ : V →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun y => fun j => dotR (y : ι → ℝ) (((b j : ↥K) : ι → ℝ))
      map_add' := fun y z => by
        funext j
        show dotR ((y + z : V) : ι → ℝ) (((b j : ↥K) : ι → ℝ))
          = dotR ((y : V) : ι → ℝ) (((b j : ↥K) : ι → ℝ))
            + dotR ((z : V) : ι → ℝ) (((b j : ↥K) : ι → ℝ))
        rw [Submodule.coe_add, dotR_add_left]
      map_smul' := fun c y => by
        funext j
        show dotR (((c • y : V)) : ι → ℝ) (((b j : ↥K) : ι → ℝ))
          = c * dotR ((y : V) : ι → ℝ) (((b j : ↥K) : ι → ℝ))
        rw [Submodule.coe_smul, dotR_smul_left] }
  have hΨval : ∀ (y : V) (j : Fin n), Ψ y j = dotR (y : ι → ℝ) (((b j : ↥K) : ι → ℝ)) :=
    fun _ _ => rfl
  have hΨinj : Function.Injective Ψ := by
    intro y z hyz
    have hdiff : Ψ (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    have h1 : ∀ j, dotR ((y - z : V) : ι → ℝ) (((b j : ↥K) : ι → ℝ)) = 0 := fun j => by
      rw [← hΨval (y - z) j, hdiff]
      rfl
    have hperp : dotR ((y - z : V) : ι → ℝ) ((y - z : V) : ι → ℝ) = 0 := by
      have hmem : ((y - z : V) : ι → ℝ)
          ∈ Submodule.span ℝ (Set.range fun j => ((b j : ↥K) : ι → ℝ)) := by
        rw [← hspanV]
        exact (y - z).2
      refine Submodule.span_induction (p := fun x _ => dotR ((y - z : V) : ι → ℝ) x = 0)
        ?_ ?_ ?_ ?_ hmem
      · rintro x ⟨j, rfl⟩; exact h1 j
      · simp
      · intro a c _ _ ha hc; rw [dotR_add_right, ha, hc, add_zero]
      · intro c a _ ha; rw [dotR_smul_right, ha, mul_zero]
    have hzero : (y - z : V) = 0 := Subtype.ext (dotR_self_eq_zero.mp hperp)
    exact sub_eq_zero.mp hzero
  have hVfin : Module.finrank ℝ V = n := by
    have h1 : Module.finrank ℝ V = rkR K := rfl
    rw [h1, hrkK]
  have hfin : Module.finrank ℝ V = Module.finrank ℝ (Fin n → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hVfin]
  set i0 : Fin n := ⟨0, hn1⟩ with hi0
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hΨinj
    (Pi.single i0 1)
  have hyj : ∀ j, dotR (y : ι → ℝ) (((b j : ↥K) : ι → ℝ))
      = (Pi.single i0 (1 : ℝ) : Fin n → ℝ) j :=
    fun j => by rw [← hΨval y j, hy]
  refine ⟨(y : ι → ℝ), ⟨y.2, fun z hz => ?_⟩, ?_⟩
  · rw [← hspanZ] at hz
    refine Submodule.span_induction (p := fun x _ => ∃ k : ℤ, dotR (y : ι → ℝ) x = (k : ℝ))
      ?_ ?_ ?_ ?_ hz
    · rintro x ⟨j, rfl⟩
      by_cases hj : j = i0
      · exact ⟨1, by rw [hyj j, hj, Pi.single_eq_same]; norm_num⟩
      · exact ⟨0, by rw [hyj j, Pi.single_eq_of_ne hj]; norm_num⟩
    · exact ⟨0, by simp⟩
    · rintro a c _ _ ⟨k1, h1⟩ ⟨k2, h2⟩
      exact ⟨k1 + k2, by rw [dotR_add_right, h1, h2]; push_cast; ring⟩
    · intro m a _ ⟨k, hk⟩
      exact ⟨m * k, by
        rw [← Int.cast_smul_eq_zsmul ℝ m a, dotR_smul_right, hk]; push_cast; ring⟩
  · intro hy0
    have h1 : (Pi.single i0 (1 : ℝ) : Fin n → ℝ) i0 = 1 := Pi.single_eq_same ..
    rw [← hyj i0, hy0, dotR_zero_left] at h1
    exact one_ne_zero h1.symm

end Work.HP.FM3
