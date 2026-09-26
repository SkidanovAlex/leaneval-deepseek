import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.LayerCont.InteriorDD.Cleanliness
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2

set_option linter.unusedSimpArgs false

namespace Work.CKFinal

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Filter

noncomputable section

/-! ## The defect operator `S(T-I)²` preserves holomorphy

`S2op k F = F|_k S(T-I)²` is the weight-`k` slash of `F` by the group-algebra element
`R_S (R_T - 1)²` of `R = ℂ[SL(2,ℤ)]`, hence a finite linear combination of the slashes
`F ↦ F ∣[k] γ`.  Each of those preserves holomorphy (`MDifferentiable.slash`). -/

private lemma mdifferentiable_slash {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (r : Work.Kernels.R) :
    MDiff (Work.Kernels.slash k r F) := by
  refine MonoidAlgebra.induction_on (motive := fun r => MDiff (Work.Kernels.slash k r F)) r ?_ ?_ ?_
  · intro m
    rw [MonoidAlgebra.of_apply, Work.Kernels.slash_single]
    simpa only [ModularForm.SL_slash, one_smul] using (hF.slash k (m : GL (Fin 2) ℝ))
  · intro x y hx hy
    rw [Work.Kernels.slash_add]
    exact hx.add hy
  · intro c x hx
    rw [Work.Kernels.AlgebraFacts.slash_smul]
    exact hx.const_smul c

/-- The defect operator `S(T-I)²` preserves holomorphy. -/
private lemma mdifferentiable_S2op (k : ℤ) {F : ℍ → ℂ} (hF : MDiff F) :
    MDiff (Work.Asymptotics.S2op k F) :=
  mdifferentiable_slash hF k _

/-! ## The identity theorem on `ℍ` -/

/-- **The identity theorem for holomorphic functions on `ℍ`.**  A holomorphic `G : ℍ → ℂ` that
vanishes on a nonempty open subset of `ℍ` vanishes identically. -/
private lemma eq_zero_of_eqOn_isOpen {G : ℍ → ℂ} (hG : MDiff G) {V : Set ℍ} (hV : IsOpen V)
    (hne : V.Nonempty) (hzero : ∀ τ ∈ V, G τ = 0) : G = 0 := by
  obtain ⟨τ₀, hτ₀⟩ := hne
  have hVnhds : V ∈ 𝓝 τ₀ := IsOpen.mem_nhds hV hτ₀
  have hev : G =ᶠ[𝓝 τ₀] 0 := by
    filter_upwards [show ∀ᶠ x in 𝓝 τ₀, x ∈ V from hVnhds] with τ hτ
    exact hzero τ hτ
  exact UpperHalfPlane.eq_zero_of_frequently hG (hev.filter_mono nhdsWithin_le_nhds).frequently

/-- The open set `{τ ∈ 𝒟 : Re τ ≠ 0}` is nonempty: `1/2 + 2i` lies in `𝒟`. -/
private lemma exists_mem_DomainD_re_ne_zero :
    ∃ σ : ℍ, σ ∈ Work.Asymptotics.DomainD ∧ σ.re ≠ 0 := by
  set z : ℂ := (1 / 2 : ℂ) + 2 * Complex.I with hz
  have hzim : z.im = 2 := by
    rw [hz]; simp [Complex.add_im, Complex.mul_im]
  have hzre : z.re = 1 / 2 := by
    rw [hz]; simp [Complex.add_re, Complex.mul_re]
  refine ⟨⟨z, by rw [hzim]; norm_num⟩, ?_, ?_⟩
  · rw [Work.Asymptotics.mem_DomainD]
    have hcoe : ((⟨z, by rw [hzim]; norm_num⟩ : ℍ) : ℂ) = z := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (-1 : ℝ) < z.re; rw [hzre]; norm_num
    · change z.re < 1; rw [hzre]; norm_num
    · have hsq : ‖z - (1 / 2 : ℂ)‖ ^ 2 = (2 : ℝ) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz]
        simp [Complex.mul_re, Complex.mul_im]
        norm_num
      rw [hcoe]
      nlinarith [norm_nonneg (z - (1 / 2 : ℂ))]
    · have hsq : (1 / 2 : ℝ) ^ 2 < ‖z + (1 / 2 : ℂ)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz]
        simp [Complex.mul_re, Complex.mul_im]
        norm_num
      rw [hcoe]
      nlinarith [norm_nonneg (z + (1 / 2 : ℂ))]
  · change z.re ≠ 0
    rw [hzre]; norm_num

/-! ## The main theorem -/

/-- **From clean points to all points.**  If `S(T-I)²` annihilates every cusp coefficient function
`Gcusp ℓ d i j` at every point `τ` whose `SL(2,ℤ)`-orbit misses the imaginary axis, then it
annihilates them everywhere.

Route: `S2op ((d:ℤ)/2) (Gcusp ℓ d i j)` is holomorphic on `ℍ` (`mdifferentiable_Gcusp` and
holomorphy of the slash by `R_S (R_T − 1)²`, i.e. of a translation of `Gcusp ℓ d i j ∣[d/2] S`); it
vanishes on the nonempty open set `{τ ∈ 𝒟 : Re τ ≠ 0}`
(`InteriorDD.jInvariantFun_ne_imagAxis_of_mem_DomainD`), so the identity theorem
(`UpperHalfPlane.eq_zero_of_frequently`) gives vanishing everywhere. -/
theorem S2op_Gcusp_all_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hclean : ∀ (τ : UpperHalfPlane) (i j : Fin 2),
      (∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) →
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) τ = 0) :
    ∀ (τ : UpperHalfPlane) (i j : Fin 2),
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) τ = 0 := by
  intro τ i j
  -- the defect is holomorphic on `ℍ`
  have hGmd : MDiff (fun σ : ℍ => Work.Asymptotics.S2op ((d : ℤ) / 2)
      (Work.Asymptotics.Gcusp ℓ d i j) σ) :=
    mdifferentiable_S2op _ (Work.LayerCont.mdifferentiable_Gcusp ℓ d hd i j)
  -- the open set `{σ ∈ 𝒟 : Re σ ≠ 0}`
  have hVopen : IsOpen {σ : ℍ | σ ∈ Work.Asymptotics.DomainD ∧ σ.re ≠ 0} :=
    Work.Asymptotics.isOpen_DomainD.inter
      (IsOpen.preimage UpperHalfPlane.continuous_re isOpen_ne)
  -- the defect vanishes there, by the cleanness hypothesis
  have hVzero : ∀ σ ∈ {σ : ℍ | σ ∈ Work.Asymptotics.DomainD ∧ σ.re ≠ 0},
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) σ = 0 :=
    fun σ hσ => hclean σ i j (fun t ht =>
      Work.LayerCont.InteriorDD.jInvariantFun_ne_imagAxis_of_mem_DomainD hσ.1 hσ.2 t ht)
  have hG0 := eq_zero_of_eqOn_isOpen hGmd hVopen exists_mem_DomainD_re_ne_zero hVzero
  exact congrFun hG0 τ

end

end Work.CKFinal
