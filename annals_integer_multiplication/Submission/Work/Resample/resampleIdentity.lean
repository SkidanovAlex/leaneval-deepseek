import Mathlib
import Submission.Work.Resample.defs
import Submission.Work.Resample.dftTensor
import Submission.Work.Resample.tensorComp
import Submission.Work.Resample.tensorSmul
import Submission.Work.Resample.resample1DEntry
import Submission.Work.Resample.tensorChain
import Submission.Work.Resample.tensorLinCongr

namespace Work.Resample

/-- **Theorem 4.1 (identity).** The multidimensional DFT on the `ss`-grid factors through the
tensor resampling maps:
`F_s = 2^{2Dα²} ∘ B ∘ F_t ∘ A`, where `A = ⊗ resA sᵢ tᵢ α`, `B = ⊗ resB sᵢ tᵢ α`.

This is the tensor product of the one-dimensional identities `F_{sᵢ} = 2^{2α²} Bᵢ F_{tᵢ} Aᵢ`
of `HvdH.ResMath1DProp`, using the tensor factorisation of `dftMulti` (`dftTensor`), the
composition law for tensors (`tensorComp`) and the scalar law (`tensorSmul`). -/
theorem resampleIdentity (p α : ℕ) (ss ts : List ℕ) (h : HvdH.ResParams p α ss ts)
    (hM : HvdH.ResMath1DProp) (u : Fin ss.prod → ℂ) :
    HvdH.dftMulti ss (-1) u =
      (2 : ℂ) ^ (2 * HvdH.D * α ^ 2) •
        Work.Resample.resBop ss ts α (HvdH.dftMulti ts (-1) (Work.Resample.resAop ss ts α u)) := by
  -- positivity of the dimension entries, needed for the tensor factorisation of `dftMulti`
  have hpos_ss : ∀ t ∈ ss, 0 < t := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have hiD : i < HvdH.D := h.1 ▸ hi
    have h2 : 2 ≤ ss.getD i 0 := (h.2.2.2.2.2 i hiD).1
    rw [List.getD_eq_getElem _ _ hi] at h2
    omega
  have hpos_ts : ∀ t ∈ ts, 0 < t := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have hiD : i < HvdH.D := h.2.1 ▸ hi
    have h2 : 2 ≤ ss.getD i 0 := (h.2.2.2.2.2 i hiD).1
    have h3 : ss.getD i 0 < ts.getD i 0 := (h.2.2.2.2.2 i hiD).2.1
    rw [List.getD_eq_getElem _ _ hi] at h3
    omega
  -- the single scalar of the one-dimensional identities
  set d : ℂ := 1 / (2 : ℂ) ^ (2 * α ^ 2) with hd
  -- the entrywise one-dimensional identity, in the shape consumed by `tensorLin`
  have hpt : ∀ i < ss.length, ∀ j k,
      (fun i j k => ∑ l : Fin (ts.getD i 0),
        Work.Resample.rB (ss.getD i 0) (ts.getD i 0) α j l *
          (∑ l2 : Fin (ts.getD i 0), Work.Resample.dE (ts.getD i 0) l l2 *
            Work.Resample.rA (ss.getD i 0) (ts.getD i 0) α l2 k)) i j k
      = (fun i j k => d * Work.Resample.dE (ss.getD i 0) j k) i j k := by
    intro i hi j k
    have hiD : i < HvdH.D := h.1 ▸ hi
    have h1 := congrFun (congrFun (resample1DEntry p α ss ts h hM i hiD) j) k
    simpa [hd] using h1
  -- `B (F_t (A u))` is the tensor of the products `resBᵢ · dftMat tᵢ · resAᵢ`
  have hc := Work.Resample.tensorLinCongr (ts := ss) hpt u
  -- and that tensor is `d^D` times the tensor of the `dftMat sᵢ`
  have hts : Work.Resample.tensorLin ss ss (fun i j k => d * Work.Resample.dE (ss.getD i 0) j k) u
      = d ^ ss.length • Work.Resample.dftOp ss u := by
    have := Work.Resample.tensorSmul ss ss d (fun i j k => Work.Resample.dE (ss.getD i 0) j k) u
    simpa [Work.Resample.dftOp] using this
  have hsc : (2 : ℂ) ^ (2 * HvdH.D * α ^ 2) * d ^ ss.length = 1 := by
    rw [h.1, hd]
    have hy : (1 / (2 : ℂ) ^ (2 * α ^ 2)) ^ HvdH.D = ((2 : ℂ) ^ (2 * α ^ 2 * HvdH.D))⁻¹ := by
      rw [one_div, inv_pow, ← pow_mul]
    rw [hy]
    have he : 2 * HvdH.D * α ^ 2 = 2 * α ^ 2 * HvdH.D := by ring
    rw [he, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]
  -- tensor factorisation of both `dftMulti`s
  rw [Work.Resample.dftTensor ss hpos_ss u,
      Work.Resample.dftTensor ts hpos_ts (Work.Resample.resAop ss ts α u)]
  -- identify `B ∘ F_t ∘ A` with the tensor of `resBᵢ · dftMat tᵢ · resAᵢ`
  have hlen : ss.length = ts.length := by rw [h.1, h.2.1]
  rw [← Work.Resample.tensorChain ss ts α hlen u]
  rw [hc]
  rw [hts]
  rw [smul_smul, hsc, one_smul]

end Work.Resample
