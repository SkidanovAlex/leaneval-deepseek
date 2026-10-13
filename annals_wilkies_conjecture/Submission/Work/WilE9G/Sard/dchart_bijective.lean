import Mathlib
import Submission.Work.WilE9G.Sard.rankDefs

set_option autoImplicit false

noncomputable section

namespace Work.WilE9G.Sard

/-- `kdrj j` is the same as deleting the `j`-th coordinate, i.e. `Fin.removeNth`. -/
theorem kdrj_eq_removeNth {d : ℕ} (j : Fin (d + 1)) (v : Fin (d + 1) → ℝ) :
    kdrj j v = j.removeNth v := by
  funext l
  rw [kdrj_apply, crj_apply, Fin.removeNth_apply]

/-- Inserting `c` in position `j` and `0` elsewhere is `c • Pi.single j 1`. -/
theorem insertNth_zero_eq_smul {d : ℕ} (j : Fin (d + 1)) (c : ℝ) :
    (Fin.insertNth j c (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) = c • Pi.single j (1 : ℝ) := by
  refine Fin.insertNth_eq_iff.2 ⟨?_, ?_⟩
  · simp [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  · funext l
    simp only [Fin.removeNth_apply, Pi.smul_apply, Pi.single_eq_of_ne (Fin.succAbove_ne j l),
      smul_zero, Pi.zero_apply]

theorem dchart_bijective {d m : ℕ} (A : (Fin (d + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ))
    (i : Fin (m + 1)) (j : Fin (d + 1)) (hij : A (Pi.single j (1 : ℝ)) i ≠ 0) :
    Function.Bijective ((kdrj j).prod ((ContinuousLinearMap.proj i).comp A)) := by
  have hT : ∀ x, (kdrj j).prod ((ContinuousLinearMap.proj i).comp A) x = (kdrj j x, (A x) i) := by
    intro x
    simp
  constructor
  · -- injectivity
    intro v w hvw
    rw [hT v, hT w] at hvw
    have h1 : kdrj j v = kdrj j w := congrArg Prod.fst hvw
    have h2 : (A v) i = (A w) i := congrArg Prod.snd hvw
    have hker : kdrj j (v - w) = 0 := by simp [map_sub, h1]
    have hrm : j.removeNth (v - w) = 0 := by
      rw [← kdrj_eq_removeNth j (v - w)]
      exact hker
    have hdecomp : v - w = Fin.insertNth j ((v - w) j) (0 : Fin d → ℝ) :=
      Fin.eq_insertNth_iff.2 ⟨rfl, hrm⟩
    have hA' : A (v - w) = ((v - w) j) • A (Pi.single j (1 : ℝ)) := by
      conv_lhs => rw [hdecomp]
      rw [insertNth_zero_eq_smul j ((v - w) j)]
      simp
    have hcoord : (A (v - w)) i = ((v - w) j) * (A (Pi.single j (1 : ℝ))) i := by
      rw [hA']
      simp [smul_eq_mul]
    have hA0 : (A (v - w)) i = 0 := by simp [map_sub, h2]
    have hc0 : (v - w) j = 0 := by
      have h : ((v - w) j) * (A (Pi.single j (1 : ℝ))) i = 0 := by
        rw [← hcoord]
        exact hA0
      exact (mul_eq_zero.mp h).resolve_right hij
    have hvjeq : v j = w j := by
      have h : v j - w j = 0 := by simpa using hc0
      exact sub_eq_zero.mp h
    have hrem : j.removeNth v = j.removeNth w := by
      rw [← kdrj_eq_removeNth j v, ← kdrj_eq_removeNth j w]
      exact h1
    calc v = Fin.insertNth j (v j) (j.removeNth v) := (Fin.insertNth_eq_iff.2 ⟨rfl, rfl⟩).symm
      _ = Fin.insertNth j (w j) (j.removeNth w) := by rw [hvjeq, hrem]
      _ = w := Fin.insertNth_eq_iff.2 ⟨rfl, rfl⟩
  · -- surjectivity
    rintro ⟨u, t⟩
    set v₀ : Fin (d + 1) → ℝ := Fin.insertNth j (0 : ℝ) u with hv₀
    set c : ℝ := (t - (A v₀) i) / (A (Pi.single j (1 : ℝ))) i with hc
    have hv₀u : kdrj j v₀ = u := by rw [hv₀, kdrj_eq_removeNth, Fin.removeNth_insertNth]
    have hsk : kdrj j (Pi.single j (1 : ℝ)) = 0 := by
      funext l
      simp only [kdrj_apply, crj_apply, Pi.single_eq_of_ne (Fin.succAbove_ne j l), Pi.zero_apply]
    have h1 : kdrj j (v₀ + c • Pi.single j (1 : ℝ)) = u := by simp [hv₀u, hsk]
    have hsplit : (A (v₀ + c • Pi.single j (1 : ℝ))) i
        = (A v₀) i + c * (A (Pi.single j (1 : ℝ))) i := by simp [smul_eq_mul]
    have h2 : (A (v₀ + c • Pi.single j (1 : ℝ))) i = t := by
      rw [hsplit, hc, div_mul_cancel₀ (t - (A v₀) i) hij]
      ring
    exact ⟨v₀ + c • Pi.single j (1 : ℝ), by rw [hT]; exact Prod.ext h1 h2⟩

end Work.WilE9G.Sard
