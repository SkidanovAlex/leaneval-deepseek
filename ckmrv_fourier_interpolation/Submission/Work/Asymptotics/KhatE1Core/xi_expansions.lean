import Submission.Work.Asymptotics.KhatE1.KdevE2Expansions

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# The theta quartics `ξ₂`, `ξ₄` up to order `e⁴`

`ξ₂ = U + W = θ₀₀⁴ + θ₀₁⁴` and `ξ₄ = U² + W² - 2V² = θ₀₀⁸ + θ₀₁⁸ - 2θ₁₀⁸` are the `τ`-atom
factors of `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S` and `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S`
(`Work.Kernels.psi2`, `psi4`).  This file records, on the funnel, the expansions of `ξ₂` and
`ξ₄` through the `E(z)⁴ = q²` term:

  `ξ₂ = 2 + 48q + 48q² + O(e⁵)`,  `ξ₄ = 2 - 288q - 1824q² + O(e⁵)`,  `e = Ept τ`, `q = e²`,

obtained immediately from the workspace's `Ufun_exp5`, `Wfun_exp5`, `Vfun_exp5`
(`U = 1+8e+24e²+32e³+24e⁴+O(e⁵)`, `W = 1-8e+24e²-32e³+24e⁴+O(e⁵)`, `V = 16e+64e³+O(e⁵)`).
These are the `U`/`W`/`V` inputs of `psi_second_order`. -/

/-- **`ξ₂` through `e⁴`**: `U + W = 2 + 48q + 48q² + O(e⁵)`. -/
theorem xi2_expansion :
    IsSm 5 (fun τ : ℍ => Work.Kernels.xi2Fun τ
      - (2 + 48 * Work.Residues.Ept τ ^ 2 + 48 * (Work.Residues.Ept τ ^ 2) ^ 2)) := by
  have h := Ufun_exp5.add Wfun_exp5
  refine h.congr (fun τ => ?_)
  simp only [Work.Kernels.xi2Fun]
  ring

/-- `ξ₄` through `e⁴`**: `U² + W² - 2V² = 2 - 288q - 1824q² + O(e⁵)`. -/
theorem xi4_expansion :
    IsSm 5 (fun τ : ℍ => Work.Kernels.xi4Fun τ
      - (2 - 288 * Work.Residues.Ept τ ^ 2 - 1824 * (Work.Residues.Ept τ ^ 2) ^ 2)) := by
  have hu0 : IsSm 0 (fun τ : ℍ => (1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
      + 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ)) :=
    ((((IsSm.one.add (isSm_Ept.const_mul 8)).add
      ((isSm_Ept.pow 2).const_mul 24)).add
      ((isSm_Ept.pow 3).const_mul 32)).add
      ((isSm_Ept.pow 4).const_mul 24))
  have hw0 : IsSm 0 (fun τ : ℍ => (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
      - 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ)) :=
    ((((IsSm.one.sub (isSm_Ept.const_mul 8)).add
      ((isSm_Ept.pow 2).const_mul 24)).sub
      ((isSm_Ept.pow 3).const_mul 32)).add
      ((isSm_Ept.pow 4).const_mul 24))
  have hv0 : IsSm 0 (fun τ : ℍ => (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ)) :=
    ((isSm_Ept.const_mul 16).add ((isSm_Ept.pow 3).const_mul 64)).mono (Nat.zero_le _)
  have hU : IsSm 5 (fun τ : ℍ => Work.Kernels.UFun τ
      - (1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
        + 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ)) :=
    Ufun_exp5.congr (fun τ => by ring)
  have hW : IsSm 5 (fun τ : ℍ => Work.Kernels.WFun τ
      - (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
        - 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ)) :=
    Wfun_exp5.congr (fun τ => by ring)
  have hV : IsSm 5 (fun τ : ℍ => Work.Kernels.VFun τ
      - (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ)) :=
    Vfun_exp5.congr (fun τ => by ring)
  have hUp : IsSm 0 (fun τ : ℍ => Work.Kernels.UFun τ + (1 + 8 * Work.Residues.Ept τ
      + 24 * Work.Residues.Ept τ ^ 2 + 32 * Work.Residues.Ept τ ^ 3
      + 24 * Work.Residues.Ept τ ^ 4 : ℂ)) :=
    ((hU.mono (Nat.zero_le 5)).add (hu0.const_mul 2)).congr (fun τ => by ring)
  have hWp : IsSm 0 (fun τ : ℍ => Work.Kernels.WFun τ + (1 - 8 * Work.Residues.Ept τ
      + 24 * Work.Residues.Ept τ ^ 2 - 32 * Work.Residues.Ept τ ^ 3
      + 24 * Work.Residues.Ept τ ^ 4 : ℂ)) :=
    ((hW.mono (Nat.zero_le 5)).add (hw0.const_mul 2)).congr (fun τ => by ring)
  have hVp : IsSm 0 (fun τ : ℍ => Work.Kernels.VFun τ
      + (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ)) :=
    ((hV.mono (Nat.zero_le 5)).add (hv0.const_mul 2)).congr (fun τ => by ring)
  have hUsq : IsSm 5 (fun τ : ℍ => Work.Kernels.UFun τ ^ 2
      - (1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
        + 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2) :=
    (hU.mul hUp).congr (fun τ => by ring)
  have hWsq : IsSm 5 (fun τ : ℍ => Work.Kernels.WFun τ ^ 2
      - (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
        - 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2) :=
    (hW.mul hWp).congr (fun τ => by ring)
  have hVsq : IsSm 5 (fun τ : ℍ => Work.Kernels.VFun τ ^ 2
      - (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ) ^ 2) :=
    (hV.mul hVp).congr (fun τ => by ring)
  -- the residual of the e-polynomials: `u₀²+w₀²-2v₀² - (2-288q-1824q²) = -3840e⁶ + 1152e⁸`
  have hpoly : IsSm 5 (fun τ : ℍ =>
      (1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
          + 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2
      + (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
          - 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2
      - 2 * (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ) ^ 2
      - (2 - 288 * Work.Residues.Ept τ ^ 2 - 1824 * (Work.Residues.Ept τ ^ 2) ^ 2)) :=
    (((isSm_Epow (-3840) 6).add (isSm_Epow 1152 8)).mono (by norm_num)).congr
      (fun τ => by ring)
  have hsum : IsSm 5 (fun τ : ℍ =>
      (Work.Kernels.UFun τ ^ 2 - (1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
          + 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2)
      + (Work.Kernels.WFun τ ^ 2 - (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
          - 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2)
      - 2 * (Work.Kernels.VFun τ ^ 2
          - (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ) ^ 2)
      + ((1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
            + 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2
          + (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
            - 32 * Work.Residues.Ept τ ^ 3 + 24 * Work.Residues.Ept τ ^ 4 : ℂ) ^ 2
          - 2 * (16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3 : ℂ) ^ 2
          - (2 - 288 * Work.Residues.Ept τ ^ 2 - 1824 * (Work.Residues.Ept τ ^ 2) ^ 2))) :=
    ((hUsq.add hWsq).sub (hVsq.const_mul 2)).add hpoly
  refine hsum.congr (fun τ => ?_)
  simp only [Work.Kernels.xi4Fun]
  ring

end

end Work.Asymptotics.KhatE1
