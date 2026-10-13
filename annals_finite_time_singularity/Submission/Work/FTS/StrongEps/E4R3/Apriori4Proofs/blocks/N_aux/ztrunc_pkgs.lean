import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ZTrunc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)
open scoped Real Topology

set_option autoImplicit false

/-! # `N_aux.ZTruncPkgs` — the elliptic packages are invariant under `ztrunc`

`ztrunc w z θ = if 0 < z then w z θ else 0` agrees with `w` on the whole half-plane `z > 0`.
Everything the two elliptic packages see is either

* the source itself, evaluated **on the open quadrant** (`IsBslSol`'s equation, the vanishing of
  `Uop`'s θ-traces, the `CoefTh`/`CoefThMem` fields), or
* a local operator applied to the residual `PhiTil α w Φg` (`Rop`, `Uop`, `Vop`), or
* an integral / `L²`-type quantity (`HkSq`, `Xn`, `HkMem`), which is blind to the null set
  `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`.

The whole content is therefore the agreement of `PhiTil α (ztrunc w) Φg` with
`PhiTil α w Φg` on `z > 0`, which follows from `L₁₂ (ztrunc w) z = L₁₂ w z` for `z ≥ 0`: the
defining integral of `L₁₂` runs over `s > z ≥ 0`, where `ztrunc w = w`.

The congruence lemmas below are stated for agreement on the whole half-plane `{z > 0}` (which is
what we actually have here); they are the τ-free analogues of the quadrant lemmas of
`Work.FTS_RegExport.RXR5`.
-/

section Helpers

/-- `L₁₂`'s angular density only sees the values of the source at `s > 0`. -/
theorem L12dens_ztrunc (w : Fn) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (ztrunc w) s = Work.Construction.L12dens w s := by
  unfold Work.Construction.L12dens Work.FM.L12dens
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [ztrunc_of_pos hs])

/-- `L₁₂` is unchanged by the truncation for every `z ≥ 0`. -/
theorem L12_ztrunc (w : Fn) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (ztrunc w) z = Work.Construction.L12 w z := by
  unfold Work.Construction.L12 Work.FM.L12
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => L12dens_ztrunc w (lt_of_le_of_lt hz hs))

/-- The singular part `Θ` is unchanged by the truncation. -/
theorem Theta_ztrunc (α : ℝ) (w : Fn) {z θ : ℝ} (hz : 0 ≤ z) :
    Work.Construction.Theta α (ztrunc w) z θ = Work.Construction.Theta α w z θ := by
  simp only [Work.Construction.Theta, L12_ztrunc w hz]

/-- The elliptic residual `PhiTil` is unchanged by the truncation on the half-plane `z > 0`. -/
theorem PhiTil_ztrunc (α : ℝ) (w Φg : Fn) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.PhiTil α (ztrunc w) Φg z θ
      = Work.Construction.PhiTil α w Φg z θ := by
  intro z θ hz
  simp only [Work.Construction.PhiTil, Theta_ztrunc α w hz.le]

/-! ### The residual on the two angular boundary lines -/

/-- `PhiTil` reduces to `Φ` on the line `θ = 0` (the `sin 2θ`-factor of `Θ` vanishes). -/
theorem PhiTil_line_zero (α : ℝ) (F Φ : Fn) (z : ℝ) :
    Work.Construction.PhiTil α F Φ z 0 = Φ z 0 := by
  simp [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]

/-- `PhiTil` reduces to `Φ` on the line `θ = π/2`. -/
theorem PhiTil_line_halfpi (α : ℝ) (F Φ : Fn) (z : ℝ) :
    Work.Construction.PhiTil α F Φ z (π / 2) = Φ z (π / 2) := by
  simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have h : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  rw [h, mul_zero, zero_mul, sub_zero]

/-! ### Locality of the operators of §Modulation -/

/-- Agreement on the half-plane `z > 0` gives agreement of `∂_z`. -/
theorem pz_congr_half {Ψ Ψ' : Fn} (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ)
    (z θ : ℝ) (hz : 0 < z) : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ := by
  simp only [Work.Spaces.pz]
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ hz')

/-- Agreement on the half-plane `z > 0` gives agreement of `∂_θ`. -/
theorem pth_congr_half {Ψ Ψ' : Fn} (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ)
    (z θ : ℝ) (hz : 0 < z) : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ := by
  simp only [Work.Spaces.pth]
  exact Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall (fun θ' => h z θ' hz))

/-- `Rop` is local on the half-plane `z > 0`. -/
theorem Rop_congr_half {α : ℝ} {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.Rop α Ψ z θ = Work.Construction.Rop α Ψ' z θ := by
  intro z θ hz
  have hpz : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ := pz_congr_half h z θ hz
  have hpth : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ := pth_congr_half h z θ hz
  simp only [Work.Construction.Rop]
  rw [h z θ hz, hpz, hpth]

/-- `Uop` is local on the half-plane `z > 0`. -/
theorem Uop_congr_half {α : ℝ} {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.Uop α Ψ z θ = Work.Construction.Uop α Ψ' z θ := by
  intro z θ hz
  have hpz : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ := pz_congr_half h z θ hz
  simp only [Work.Construction.Uop]
  rw [h z θ hz, hpz]

/-- `Vop` is local on the half-plane `z > 0`. -/
theorem Vop_congr_half {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.Vop Ψ z θ = Work.Construction.Vop Ψ' z θ := by
  intro z θ hz
  have hpth : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ := pth_congr_half h z θ hz
  simp only [Work.Construction.Vop]
  rw [h z θ hz, hpth]

/-- `Uop / sin 2θ` is local on the half-plane `z > 0`. -/
theorem Uop_div_s2_congr_half {α : ℝ} {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z →
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α Ψ' z θ / Work.Construction.s2 θ :=
  fun z θ hz => by rw [Uop_congr_half h z θ hz]

/-! ### The flat angular norms

`supAbsO` is the supremum over the *open* quadrant and `CoefTh`/`CoefThMem` are built from
`supAbsO (D_z^b D_θ^i ∂_θ ·)`, so all three only see the open quadrant. -/

/-- `supAbsO` only depends on the values on the open quadrant. -/
theorem supAbsO_congr_trunc {f f' : Fn} (h : Work.FTS.EllipticEst.AgreeOnQ f f') :
    Work.FTS.H2.supAbsO f = Work.FTS.H2.supAbsO f' := by
  unfold Work.FTS.H2.supAbsO
  have hset : {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |f z θ|}
      = {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |f' z θ|} := by
    ext y
    constructor
    · rintro ⟨z, hz, θ, hθ, hθ', rfl⟩
      exact ⟨z, hz, θ, hθ, hθ', by rw [h z θ hz hθ hθ']⟩
    · rintro ⟨z, hz, θ, hθ, hθ', rfl⟩
      exact ⟨z, hz, θ, hθ, hθ', by rw [h z θ hz hθ hθ']⟩
  rw [hset]

/-- `CoefTh` only depends on the values on the open quadrant. -/
theorem CoefTh_congr_trunc (l : ℕ) {f f' : Fn}
    (h : Work.FTS.EllipticEst.AgreeOnQ f f') :
    Work.FTS.VocabO.CoefTh l f = Work.FTS.VocabO.CoefTh l f' := by
  simp only [Work.FTS.VocabO.CoefTh]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with _hbi
  · exact supAbsO_congr_trunc (h.pth.mixed b i)
  · rfl

/-- `CoefThMem` only depends on the values on the open quadrant. -/
theorem CoefThMem_congr_trunc (l : ℕ) {f f' : Fn}
    (h : Work.FTS.EllipticEst.AgreeOnQ f f') :
    Work.FTS.VocabO.CoefThMem l f → Work.FTS.VocabO.CoefThMem l f' := by
  intro hf b i hbi
  obtain ⟨K, hK⟩ := hf b i hbi
  refine ⟨K, fun z θ hz hθ hθ' => ?_⟩
  rw [← (h.pth.mixed b i) z θ hz hθ hθ']
  exact hK z θ hz hθ hθ'

/-! ### `VanishTheta` of `Uop`, transferred along the two boundary lines -/

/-- `Uop`'s vanishing on the two angular boundary lines only depends on the boundary values of
its argument (through the `z`-slices at `θ = 0` and `θ = π/2`). -/
theorem vanishTheta_Uop_of_line_eq {α : ℝ} {Ψ Ψ' : Fn}
    (h0 : ∀ z, Ψ z 0 = Ψ' z 0) (h1 : ∀ z, Ψ z (π / 2) = Ψ' z (π / 2))
    (hv : Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ')) :
    Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ) := by
  have key : ∀ θb : ℝ, (∀ z, Ψ z θb = Ψ' z θb) →
      ∀ z, Work.Construction.Uop α Ψ z θb = Work.Construction.Uop α Ψ' z θb := by
    intro θb hb z
    have hs : (fun z' => Ψ z' θb) = (fun z' => Ψ' z' θb) := funext hb
    have hp : Work.Spaces.pz Ψ z θb = Work.Spaces.pz Ψ' z θb := by
      simp only [Work.Spaces.pz, hs]
    simp only [Work.Construction.Uop]
    rw [hb z, hp]
  exact ⟨fun z => by rw [key 0 h0 z]; exact hv.1 z,
    fun z => by rw [key (π / 2) h1 z]; exact hv.2 z⟩

end Helpers

/-- **The two elliptic packages are invariant under the truncation `ztrunc`.**

The only place the packages see the source is through `PhiTil α g Φg = Φg - (1/(4α))·sin 2θ·L12 g`,
and `L12 (ztrunc w) z = L12 w z` for every `z ≥ 0` (the defining integral runs over `s > z ≥ 0`,
where `ztrunc w = w`).  Hence `Rop/Uop/Vop (PhiTil α (ztrunc w) Φg)` agree with the `w`-versions on
the open quadrant, and `sol : IsBslSol(·)Pos` constrains the source only through the equation on
the open quadrant.  The `Xn`/`HkNorm` right-hand sides agree by `N_aux.HkNorm_ztrunc`.

Useful lemmas: `N_aux.HkSq_ztrunc`, `N_aux.HkNorm_ztrunc`, `N_aux.Xn_ztrunc`,
`N_aux.smoothOpen_ztrunc`, `EllipticEst.RPFresh.smoothOpen_congr`,
`EllipticEst.HkSq_congr_open`, `H6Pair6Aux.HkMem_congr_Qd`, `StrongGlobal.IsBslSolPos.congr`,
`FTS_RegExport.RXR5.L12_congr_of_agreeOnQ`, and the open-strip congruence lemmas for
`pz`/`pth` (`Spaces.pz_congr_of_isOpen`, `Spaces.Dz_congr_of_isOpen`,
`EllipticEst.SmoothOpen.DzIter_congr`). -/
theorem ztrunc_pkgs {α Ce : ℝ} {w Φg : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.ClassC.ClassC α w)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hK : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg) :
    (Work.FTS.VocabO.EllPkgGo α Ce
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) Φg ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) Φg) := by
  have hPhi : ∀ z θ : ℝ, 0 < z →
      Work.Construction.PhiTil α (ztrunc w) Φg z θ = Work.Construction.PhiTil α w Φg z θ :=
    PhiTil_ztrunc α w Φg
  -- agreement of the residual on the open quadrant, in both directions
  have hPhiQ : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.PhiTil α (ztrunc w) Φg) (Work.Construction.PhiTil α w Φg) :=
    fun z θ hz _ _ => hPhi z θ hz
  have hPhiQ' : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.PhiTil α w Φg) (Work.Construction.PhiTil α (ztrunc w) Φg) :=
    fun z θ hz hθ hθ2 => (hPhiQ z θ hz hθ hθ2).symm
  -- the three transported residuals
  have hRQ : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg))
      (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) :=
    fun z θ hz _ _ => Rop_congr_half (α := α) hPhi z θ hz
  have hRQ' : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg))
      (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg)) :=
    fun z θ hz hθ hθ2 => (hRQ z θ hz hθ hθ2).symm
  have hUQ : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
        / Work.Construction.s2 θ)
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
        / Work.Construction.s2 θ) :=
    fun z θ hz _ _ => Uop_div_s2_congr_half (α := α) hPhi z θ hz
  have hUQ' : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
        / Work.Construction.s2 θ)
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
        / Work.Construction.s2 θ) :=
    fun z θ hz hθ hθ2 => (hUQ z θ hz hθ hθ2).symm
  have hVQ : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg))
      (Work.Construction.Vop (Work.Construction.PhiTil α w Φg)) :=
    fun z θ hz _ _ => Vop_congr_half hPhi z θ hz
  have hVQ' : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Vop (Work.Construction.PhiTil α w Φg))
      (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg)) :=
    fun z θ hz hθ hθ2 => (hVQ z θ hz hθ hθ2).symm
  -- ## the `ℋ⁴` package
  have hGoNew : Work.FTS.VocabO.EllPkgGo α Ce (ztrunc w) Φg := by
    obtain ⟨sol, hsmooth, hR, hU, hV, hvanishU, hVth⟩ := hgo
    obtain ⟨hs1, hs2, hs3, hs4⟩ := sol
    refine ⟨⟨fun z hz θ hθ hθ2 => ?_, hs2, hs3, hs4⟩, hsmooth, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ztrunc_of_pos hz]
      exact hs1 z hz θ hθ hθ2
    · -- the `R` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hR.1.1 hRQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hRQ' z θ hq.1 hq.2.1 hq.2.2) hR.1.2
      · have hXn : Work.FTS.Nonlin.Xn α
            (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.FTS.Nonlin.Xn α
              (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 4 hRQ]
        rw [hXn, Xn_ztrunc α w]
        exact hR.2
    · -- the `U` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hU.1.1 hUQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hUQ' z θ hq.1 hq.2.1 hq.2.2) hU.1.2
      · have hXn : Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
              / Work.Construction.s2 θ)
            = Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
                / Work.Construction.s2 θ) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 4 hUQ]
        rw [hXn, Xn_ztrunc α w]
        exact hU.2
    · -- the `V` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hV.1.1 hVQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hVQ' z θ hq.1 hq.2.1 hq.2.2) hV.1.2
      · have hXn : Work.FTS.Nonlin.Xn α
            (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.FTS.Nonlin.Xn α
              (Work.Construction.Vop (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 4 hVQ]
        rw [hXn, Xn_ztrunc α w]
        exact hV.2
    · -- `VanishTheta` of `Uop`: only the two boundary lines matter, and there `PhiTil` is `Φg`
      exact vanishTheta_Uop_of_line_eq
        (fun z => by rw [PhiTil_line_zero α (ztrunc w) Φg z, PhiTil_line_zero α w Φg z])
        (fun z => by rw [PhiTil_line_halfpi α (ztrunc w) Φg z, PhiTil_line_halfpi α w Φg z])
        hvanishU
    · -- the `CoefTh`/`CoefThMem` field of `Vop`
      refine ⟨?_, ?_⟩
      · exact CoefThMem_congr_trunc 1 hVQ' hVth.1
      · rw [CoefTh_congr_trunc 1 hVQ, Xn_ztrunc α w]
        exact hVth.2
  -- ## the `ℋ⁶` package
  have hKNew : Work.FTS.ClassC.EllPkgK α 6 Ce (ztrunc w) Φg := by
    obtain ⟨sol, hsmooth, hR, hU, hV⟩ := hK
    obtain ⟨ks1, ks2, ks3, ks4⟩ := sol
    refine ⟨⟨fun z hz θ hθ hθ2 => ?_, ks2, ks3, ks4⟩, hsmooth, ?_, ?_, ?_⟩
    · rw [ztrunc_of_pos hz]
      exact ks1 z hz θ hθ hθ2
    · -- the `R` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hR.1.1 hRQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hRQ' z θ hq.1 hq.2.1 hq.2.2) hR.1.2
      · have hN : Work.Spaces.HkNorm α 6
            (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.Spaces.HkNorm α 6
              (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 6 hRQ]
        rw [hN, HkNorm_ztrunc α 6 w]
        exact hR.2
    · -- the `U` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hU.1.1 hUQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hUQ' z θ hq.1 hq.2.1 hq.2.2) hU.1.2
      · have hN : Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
              / Work.Construction.s2 θ)
            = Work.Spaces.HkNorm α 6
              (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
                / Work.Construction.s2 θ) := by
          simp only [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 6 hUQ]
        rw [hN, HkNorm_ztrunc α 6 w]
        exact hU.2
    · -- the `V` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hV.1.1 hVQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hVQ' z θ hq.1 hq.2.1 hq.2.2) hV.1.2
      · have hN : Work.Spaces.HkNorm α 6
            (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.Spaces.HkNorm α 6
              (Work.Construction.Vop (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 6 hVQ]
        rw [hN, HkNorm_ztrunc α 6 w]
        exact hV.2
  exact ⟨hGoNew, hKNew⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
