import Mathlib
import Submission.Work.L2F.Props.oddsub.CommonEigenvectorAux
import Submission.Work.L2F.Props.oddsub.mk_eq_mk_of_eigen

namespace Work.L2F.Props.oddsub

open scoped MatrixGroups
open Matrix

variable {F : Type*} [Field F]

/-- Two nonzero eigenvectors of a **non-scalar** `2 × 2` matrix, with the same eigenvalue, span
the same line. -/
theorem mem_span_of_same_eigenvalue (M : Matrix (Fin 2) (Fin 2) F)
    (hM : ∀ c : F, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) {c : F}
    (hMv : M *ᵥ v = c • v) (hMw : M *ᵥ w = c • w) :
    w ∈ Submodule.span F ({v} : Set (Fin 2 → F)) := by
  have h : Projectivization.mk F v hv = Projectivization.mk F w hw :=
    mk_eq_mk_of_eigen F M hM hv hw hMv hMw
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F v w hv hw).mp h
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ha
    exact hv ha.symm
  exact Submodule.mem_span_singleton.mpr
    ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

theorem spans_of_two_common_eigenvectors (F : Type*) [Field F]
    (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (x : Matrix.SpecialLinearGroup (Fin 2) F) (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hxodd : Odd (orderOf x))
    (v u : Fin 2 → F) (hv : Work.L2F.Props.oddsub.IsCommonEigenvector Q v)
    (hu : Work.L2F.Props.oddsub.IsCommonEigenvector Q u)
    (huv : u ∉ Submodule.span F ({v} : Set (Fin 2 → F))) :
    ∀ z : Fin 2 → F, Work.L2F.Props.oddsub.IsCommonEigenvector Q z →
      (∃ c : F, z = c • v) ∨ (∃ c : F, z = c • u) := by
  intro z hz
  by_cases hzv : ∃ c : F, z = c • v
  · exact Or.inl hzv
  right
  by_contra hzu
  let M : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F)
  have hM : ∀ c : F, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) :=
    fun c => not_scalar_coe_of_odd_orderOf x hx1 hxodd c
  have hv0 : v ≠ 0 := hv.1
  have hu0 : u ≠ 0 := hu.1
  have hz0 : z ≠ 0 := hz.1
  obtain ⟨c, hcv⟩ := hv.2 x hxQ
  obtain ⟨d, hdu⟩ := hu.2 x hxQ
  obtain ⟨e, hdz⟩ := hz.2 x hxQ
  have hquad_c : c ^ 2 - M.trace * c + 1 = 0 :=
    sq_sub_trace_mul_add_one_of_eigenvector x v c hv0 hcv
  have hquad_d : d ^ 2 - M.trace * d + 1 = 0 :=
    sq_sub_trace_mul_add_one_of_eigenvector x u d hu0 hdu
  have hquad_e : e ^ 2 - M.trace * e + 1 = 0 :=
    sq_sub_trace_mul_add_one_of_eigenvector x z e hz0 hdz
  have hzv_span : z ∉ Submodule.span F ({v} : Set (Fin 2 → F)) := by
    rintro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact hzv ⟨a, ha.symm⟩
  have hzu_span : z ∉ Submodule.span F ({u} : Set (Fin 2 → F)) := by
    rintro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact hzu ⟨a, ha.symm⟩
  have hcd_or : c = d ∨ d = e ∨ e = c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hcd, hde, hec⟩ := hcon
    have key1 : (c - d) * (c + d - M.trace) = 0 := by
      linear_combination hquad_c - hquad_d
    have h1 : c + d = M.trace := by
      rcases mul_eq_zero.mp key1 with h | h
      · exact absurd (sub_eq_zero.mp h) hcd
      · exact sub_eq_zero.mp h
    have key2 : (d - e) * (d + e - M.trace) = 0 := by
      linear_combination hquad_d - hquad_e
    have h2 : d + e = M.trace := by
      rcases mul_eq_zero.mp key2 with h | h
      · exact absurd (sub_eq_zero.mp h) hde
      · exact sub_eq_zero.mp h
    have hce : c = e := by
      have h3 : c + d = d + e := by rw [h1, h2]
      have h4 : c + d = e + d := by rw [h3]; exact add_comm d e
      exact add_right_cancel h4
    exact hec hce.symm
  rcases hcd_or with hcd | hde | hec
  · exact huv (mem_span_of_same_eigenvalue M hM hv0 hu0 hcv (by rw [hcd]; exact hdu))
  · exact hzu_span (mem_span_of_same_eigenvalue M hM hu0 hz0 hdu (by rw [hde]; exact hdz))
  · exact hzv_span (mem_span_of_same_eigenvalue M hM hv0 hz0 hcv (by rw [← hec]; exact hdz))

end Work.L2F.Props.oddsub
