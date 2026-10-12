import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseB7AK.K1exists.tildeData_lattice_noAdd
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_jointGramLab` — the joint χ/θ coordinate model on the cube `Lab N`

`Work.BoseBoxFock.exists_honestModes` has to produce `Work.BoseBoxFock.HonestModes v μ`
on the mode set `Lab N = (ZMod (2N+1))³`, and the heart of that structure is the claim
that the χ-modes `Q(e^{ikx}χ_Λ)` and the θ-modes `e^{isx}θ` (for the cube's momenta
`kmomLab (ellH v μ) N`) can be realised *simultaneously* as coordinate vectors in a single
`ℝ^m` with their honest Gram matrices.  That is exactly the statement of this file.

The construction is the one of `Work.BoseB4.exists_gram_jointKernel`, whose hypothesis of
additivity `kmom (i - j) = kmom i - kmom j` is **false** for the wrapped cube momentum
`kmomLab` (`Lab N` is a torus: `valMinAbs` is not additive), so the `had`-free form
`Work.BoseB7AK.K1exists.exists_gram_jointKernel_noAdd` is used instead.  Its two geometric
inputs — the θ-modes are orthogonal at distinct cube labels and orthogonal to the
condensate — come from the Fourier orthogonality on the unit cube
(`Work.BoseB4.realIP_thetaExp_thetaExp_of_cell`, `..._thetaFun_of_cell`), applied after
identifying `kmomLab ℓ N n = ℓ⁻¹ • vec (labVec N n)`; distinctness of the labels is the
injectivity of `ZMod.valMinAbs`.

The results are collected in the sub-namespace `Work.BoseBoxFock.GramLab` so that they do
not collide with the same-named lemmas other files of the `BoseBoxFock` area may declare.
-/

namespace Work.BoseBoxFock

namespace GramLab

/-- `ZMod.valMinAbs` is a section of `ℤ → ZMod (2N+1)`, so the centred integer vector of a
cube label determines the label. -/
lemma labVec_injective (N : ℕ) : Function.Injective (labVec N) := by
  intro a b h
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun h i)

/-- The label `0` of the cube has centred vector `0`. -/
lemma labVec_zero (N : ℕ) : labVec N (0 : Lab N) = 0 := by
  funext i
  simp [labVec, ZMod.valMinAbs_zero]

/-- The physical momentum map of the cube is injective (`ℓ ≠ 0`, `labVec_injective`,
`Work.BoseB4.vec_injective`). -/
lemma kmomLab_injective (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) :
    Function.Injective (kmomLab ℓ N) := by
  intro a b hab
  have h1 : Work.BoseB4.vec (labVec N a) = Work.BoseB4.vec (labVec N b) := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => ℓ • z) hab
    simpa [kmomLab, smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ)] using h
  exact labVec_injective N (Work.BoseB4.vec_injective h1)

/-- `kmomLab` is the dual-lattice momentum `ℓ⁻¹ • 2π n` (definitionally). -/
lemma kmomLab_eq_smul_vec (ℓ : ℝ) (N : ℕ) (n : Lab N) :
    kmomLab ℓ N n = ℓ⁻¹ • Work.BoseB4.vec (labVec N n) := rfl

/-- The cube's momentum assignment is a dual-lattice assignment in the sense of
`Work.BoseK15.OnDualLattice` (injective, values `ℓ⁻¹ • 2π n`); this is the lattice row the
§10 gate consumes. -/
lemma kmomLab_onDualLattice (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) :
    Work.BoseK15.OnDualLattice ℓ (kmomLab ℓ N) :=
  ⟨kmomLab_injective ℓ hℓ N, fun n => ⟨labVec N n, kmomLab_eq_smul_vec ℓ N n⟩⟩

/-- **The θ-mode rows of the honest cube.**  For every `ℓ > 0` and every `N`, the θ-modes
of the cube's momenta `kmomLab ℓ N`: are orthonormal on the non-zero labels (`ℓ³` times the
Kronecker delta, the factor removed below by the normalisation `(ℓ³)^{-1/2}`), and are
orthogonal to the condensate `θ`.

Both are the unit-cube Fourier orthogonality
`Work.BoseB4.realIP_thetaExp_thetaExp_of_cell`/`..._thetaFun_of_cell` after rewriting
`kmomLab ℓ N s = ℓ⁻¹ • vec (labVec N s)`; the label comparison uses the injectivity of
`labVec N`. -/
lemma corpusBox_theta_rows (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) :
    (∀ s t : Lab N, s ≠ 0 → t ≠ 0 →
        Work.BoseK15.corpusBox.realIP
          (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s))
          (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N t))
          = if s = t then ℓ ^ 3 else 0)
    ∧ (∀ s : Lab N, s ≠ 0 →
        Work.BoseK15.corpusBox.realIP
          (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s))
          (Work.BoseK15.corpusBox.thetaFun ℓ) = 0) := by
  have hiff : ∀ s t : Lab N, labVec N s = labVec N t ↔ s = t :=
    fun s t => ⟨fun h => labVec_injective N h, fun h => by rw [h]⟩
  constructor
  · intro s t _ _
    rw [kmomLab_eq_smul_vec ℓ N s, kmomLab_eq_smul_vec ℓ N t,
        Work.BoseB4.realIP_thetaExp_thetaExp_of_cell Work.BoseK15.corpusBox rfl hℓ
          (labVec N s) (labVec N t)]
    exact if_congr (hiff s t) rfl rfl
  · intro s hs
    rw [kmomLab_eq_smul_vec ℓ N s,
        Work.BoseB4.realIP_thetaExp_thetaFun_of_cell Work.BoseK15.corpusBox rfl hℓ (labVec N s),
        if_neg]
    intro h0
    exact hs (labVec_injective N (by rw [h0, labVec_zero N]))

end GramLab

open GramLab

theorem exists_jointGramLab (v : ℝ³ → ℝ) (μ : ℝ) (N : ℕ) :
    ∃ (m : ℕ) (f g : Lab N → Fin m → ℝ),
      (∀ i j : Lab N,
          Work.BoseB4.gram (f i) (f j)
            = Work.BoseB7.ccrKernel (ellH v μ)
                Work.BoseK15.corpusBox.hatChiSq Work.BoseK15.corpusBox.hatChi
                (kmomLab (ellH v μ) N i) (kmomLab (ellH v μ) N j))
      ∧ (∀ s t : Lab N, s ≠ 0 → t ≠ 0 →
          Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
      ∧ (∀ s k : Lab N, s ≠ 0 →
          Work.BoseB4.gram (g s) (f k)
            = Work.BoseK15.corpusBox.hatChi (ellH v μ •
                (kmomLab (ellH v μ) N k - kmomLab (ellH v μ) N s))) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨horth, horthC⟩ := corpusBox_theta_rows (ellH v μ) hℓ N
  obtain ⟨m, f, g, hf, hg, hcross⟩ :=
    Work.BoseB7AK.K1exists.exists_gram_jointKernel_noAdd Work.BoseK15.corpusBox hℓ
      (kmomLab (ellH v μ) N) horth horthC
  exact ⟨m, f, g, hf, hg, hcross⟩

end Work.BoseBoxFock
