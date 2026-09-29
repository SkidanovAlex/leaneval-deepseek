import Mathlib
import Submission.Work.Transform.phiZipDefs

namespace Work.Transform

theorem phiZExtract {p M r : ℕ} {a b : List (List (ℤ × ℤ))} {zs : List HvdH.Val}
    (ha : a.length = M) (hb : b.length = M) (hlen : zs.length = M)
    (hQ : ∀ i < M, Work.Transform.PhiZQ p r ((a.map HvdH.cvecVal).getD i HvdH.Val.nil)
      ((b.map HvdH.cvecVal).getD i HvdH.Val.nil) (zs.getD i HvdH.Val.nil)) :
    ∃ us : List (List (ℤ × ℤ)), HvdH.ofList zs = HvdH.rarrVal us ∧ us.length = M ∧
      HvdH.InDiscArr p M r us ∧ (∀ i < M, (us.getD i []).length = r) ∧
      ∀ i < M, ∀ c < r, (2 : ℝ) ^ p * ‖HvdH.fxC p ((us.getD i []).getD c (0, 0))
        - HvdH.fxC p ((b.getD i []).getD c (0, 0)) * HvdH.fxC p ((a.getD i []).getD c (0, 0))‖ < 2 := by
  classical
  -- Read the per-index postcondition `PhiZQ` into the extracted vector `ws`.
  have hQ' : ∀ i, i < M → ∃ (ws : List (ℤ × ℤ)),
      zs.getD i HvdH.Val.nil = HvdH.cvecVal ws ∧ HvdH.InDiscVec p r ws ∧
      ∀ c < r, (2 : ℝ) ^ p * ‖HvdH.fxC p (ws.getD c (0, 0))
        - HvdH.fxC p ((b.getD i []).getD c (0, 0)) * HvdH.fxC p ((a.getD i []).getD c (0, 0))‖ < 2 := by
    intro i hi
    have hai : i < a.length := by rw [ha]; exact hi
    have hbi : i < b.length := by rw [hb]; exact hi
    obtain ⟨ws, pa, pb, hz, hx, hy, hd, he⟩ := hQ i hi
    rw [cvecVal_getD hai] at hx
    rw [cvecVal_getD hbi] at hy
    have hpa : a.getD i [] = pa := cvecVal_injective hx
    have hpb : b.getD i [] = pb := cvecVal_injective hy
    rw [← hpa] at he
    rw [← hpb] at he
    exact ⟨ws, hz, hd, he⟩
  let us : List (List (ℤ × ℤ)) := List.ofFn (fun i : Fin M => (hQ' i i.isLt).choose)
  have hus_def : us = List.ofFn (fun i : Fin M => (hQ' i i.isLt).choose) := rfl
  have hus_len : us.length = M := by rw [hus_def]; exact List.length_ofFn
  have hus_get : ∀ (i : ℕ) (hi : i < M), us.getD i [] = (hQ' i hi).choose := by
    intro i hi
    rw [hus_def,
      List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
  refine ⟨us, ?_, hus_len, ?_, ?_, ?_⟩
  · have hzsm : zs = us.map HvdH.cvecVal := by
      refine List.ext_getElem (by rw [hlen, List.length_map, hus_len]) ?_
      intro n h1 h2
      have hn : n < M := by rw [← hlen]; exact h1
      rw [← List.getD_eq_getElem (l := zs) (d := HvdH.Val.nil) h1, List.getElem_map,
        ← List.getD_eq_getElem (l := us) (d := ([] : List (ℤ × ℤ)))
          (by rw [hus_len]; exact hn), hus_get n hn]
      exact ((hQ' n hn).choose_spec).1
    rw [hzsm]
    rfl
  · exact (inDiscArr_iff hus_len).mpr fun i hi => by
      rw [hus_get i hi]; exact ((hQ' i hi).choose_spec).2.1
  · intro i hi
    rw [hus_get i hi]
    exact ((hQ' i hi).choose_spec).2.1.1
  · intro i hi c hc
    rw [hus_get i hi]
    exact ((hQ' i hi).choose_spec).2.2 c hc

end Work.Transform
