/-
# Well-definedness of the odd-weight extension formula (CKMRV, proof of Prop. 3.2(1))

Given the hypotheses of CKMRV Proposition 3.2(1) at **odd** weight `k` — an open set `O`
containing `closure 𝒟` on which the two defects of `f` agree with `h₁`, `h₂`, together with an
open neighbourhood `O_F` of `closure 𝓕` such that `Mp i • O_F ⊆ O` and such that
`γ • O_F ∩ O_F ≠ ∅` forces `γ` to be a *neighbour* of `𝓕` — the extension formula

  `F (γ • τ) = j(γ,τ)^k · Ψ(γ,τ)`   (`τ ∈ O_F`, `γ ∈ SL(2,ℤ)`)

of `Work.Asymptotics.Fodd` is **well defined**: the value `j(γ,τ)^k Ψ(γ,τ)` depends only on the
point `γ • τ`, not on the chosen presentation.

The proof is the one given in CKMRV.  If `γ • τ = γ' • τ'` with `τ, τ' ∈ O_F`, put
`δ = γ⁻¹γ'`, so that `γ' = γδ` and `δ • τ' = τ` with `τ' ∈ O_F`, `δ • τ' ∈ O_F`: thus `δ` is a
neighbour.  The cocycle `j(γδ,τ') = j(γ,δτ')·j(δ,τ')` reduces the claim to

  `Ψ(γ, δτ') = j(δ,τ')^k · Ψ(γδ, τ')`     (`★`)

which is the "slash transformation law" for `Ψ`.  To prove `(★)` one uses the three inputs

* the finite check for neighbours (`Work.Asymptotics.small_extension_odd`): for a neighbour `ν`
  and any row `i`, the row-`i` carry reduction of `f` equals `f|(Mp_i ν)` at `τ`;
* the cocycle for `rowDiffOdd` and for the carries (`Work.Asymptotics.OddCocycle`), which — via
  the odd-weight collapse `(1+z)R = 0` — identifies the carries of `γδ` with the `σ(γ)`-linear
  combination of the carries of `δ` and of `γ`;
* the multiplicativity of the automorphy factor `jFun_mul` and the slash cocycle
  `slash_mul`.

Both sides of `(★)` expand into the same `σ(γ)`-linear combination of the six basis slashes
`f|Mp_j`, evaluated at `δ • τ'`.
-/
import Mathlib
import Submission.Work.Asymptotics.SmallExtensionOdd
import Submission.Work.Asymptotics.OddAssembly
import Submission.Work.Asymptotics.OddCocycle
import Submission.Work.Asymptotics.sigmaHom_Mp_row0
import Submission.Work.Asymptotics.idealI_direct_augIdealOdd
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.exists_neighbour_nbdh_of_Propagates

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Work.Kernels
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ## The two identities for the carries

For fixed `γ δ : SL(2,ℤ)` and a point `τ`, the carry of `γδ` (in row `0`) differs from the
`σ(γ)`-linear combination of the carries of `δ` and the carry of `γ` by an element of the
collapse ideal `(1+z)R`, which acts by zero at odd weight.  Multiplying by `J = j(δ,τ)^k` turns
the `ofSL δ`-multiple of the carry of `γ` into its value at `δ • τ`, which is the term that
has to be compared with `Ψ(γ, δτ)`. -/

/-- The `(T-I)²`-carry part of the transformation law `(★)`. -/
lemma carryShift₁ {k : ℤ} (hk : Odd k) (γ δ : SL(2,ℤ)) (h₁ : ℍ → ℂ) (τ : ℍ) :
    (jFun δ (τ : ℂ)) ^ k * (slash k (carryOdd₁ (γ * δ) 0) h₁) τ
      = (jFun δ (τ : ℂ)) ^ k
          * (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (carryOdd₁ δ j) h₁) τ)
        + (slash k (carryOdd₁ γ 0) h₁) (δ • τ) := by
  have hc := carryOdd_cocycle₁ γ δ 0
  have hsub : carryOdd₁ (γ * δ) 0
      - (∑ j : Fin 6, (sigmaHom γ) 0 j • carryOdd₁ δ j + carryOdd₁ γ 0 * ofSL δ)
      ∈ augIdealOdd := by
    simpa only [sub_sub] using hc
  have hJ : (jFun δ (τ : ℂ)) ^ k ≠ 0 := zpow_ne_zero _ (jFun_ne_zero δ τ)
  have key : slash k (carryOdd₁ (γ * δ) 0) h₁ τ
      = (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (carryOdd₁ δ j) h₁) τ)
        + slash k (carryOdd₁ γ 0) h₁ (δ • τ) * (jFun δ (τ : ℂ)) ^ (-k) := by
    rw [slash_eq_of_sub_mem_augIdealOdd k hk hsub h₁, Work.Kernels.slash_add,
      Work.Kernels.slash_sum, Work.Kernels.AlgebraFacts.slash_mul, slash_ofSL]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Work.Kernels.AlgebraFacts.slash_smul, slash_apply']
  have hZ : (jFun δ (τ : ℂ)) ^ k
      * (slash k (carryOdd₁ γ 0) h₁ (δ • τ) * (jFun δ (τ : ℂ)) ^ (-k))
      = slash k (carryOdd₁ γ 0) h₁ (δ • τ) := by
    rw [_root_.zpow_neg, ← mul_assoc, mul_comm (jFun δ (τ : ℂ) ^ k), mul_assoc,
      mul_inv_cancel₀ hJ, mul_one]
  rw [key, mul_add, Finset.mul_sum, hZ]

/-- The `S(T-I)²`-carry part of the transformation law `(★)`. -/
lemma carryShift₂ {k : ℤ} (hk : Odd k) (γ δ : SL(2,ℤ)) (h₂ : ℍ → ℂ) (τ : ℍ) :
    (jFun δ (τ : ℂ)) ^ k * (slash k (carryOdd₂ (γ * δ) 0) h₂) τ
      = (jFun δ (τ : ℂ)) ^ k
          * (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (carryOdd₂ δ j) h₂) τ)
        + (slash k (carryOdd₂ γ 0) h₂) (δ • τ) := by
  have hc := carryOdd_cocycle₂ γ δ 0
  have hsub : carryOdd₂ (γ * δ) 0
      - (∑ j : Fin 6, (sigmaHom γ) 0 j • carryOdd₂ δ j + carryOdd₂ γ 0 * ofSL δ)
      ∈ augIdealOdd := by
    simpa only [sub_sub] using hc
  have hJ : (jFun δ (τ : ℂ)) ^ k ≠ 0 := zpow_ne_zero _ (jFun_ne_zero δ τ)
  have key : slash k (carryOdd₂ (γ * δ) 0) h₂ τ
      = (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (carryOdd₂ δ j) h₂) τ)
        + slash k (carryOdd₂ γ 0) h₂ (δ • τ) * (jFun δ (τ : ℂ)) ^ (-k) := by
    rw [slash_eq_of_sub_mem_augIdealOdd k hk hsub h₂, Work.Kernels.slash_add,
      Work.Kernels.slash_sum, Work.Kernels.AlgebraFacts.slash_mul, slash_ofSL]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Work.Kernels.AlgebraFacts.slash_smul, slash_apply']
  have hZ : (jFun δ (τ : ℂ)) ^ k
      * (slash k (carryOdd₂ γ 0) h₂ (δ • τ) * (jFun δ (τ : ℂ)) ^ (-k))
      = slash k (carryOdd₂ γ 0) h₂ (δ • τ) := by
    rw [_root_.zpow_neg, ← mul_assoc, mul_comm (jFun δ (τ : ℂ) ^ k), mul_assoc,
      mul_inv_cancel₀ hJ, mul_one]
  rw [key, mul_add, Finset.mul_sum, hZ]

/-! ## The six basis slashes

The multiplicativity of `σ` writes the row-`0` combination of basis slashes at `γδ` as the
`σ(γ)`-linear combination of the *rows* of `σ(δ)`; the finite check for the neighbour `δ`
(`small_extension_odd`, used once per row `i`) computes each row as `f|(Mp_i δ)`, and
`slash_mul` together with `j(δ,τ)^k·j(δ,τ)^{-k} = 1` converts `f|(Mp_i δ)` at `τ` into
`f|Mp_i` at `δ • τ`. -/

/-- The basis-slash part of the transformation law `(★)`. -/
lemma sigmaShift {k : ℤ} (hk : Odd k) {O O_F : Set ℍ} {f h₁ h₂ : ℍ → ℂ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Work.Asymptotics.Mp i) • τ ∈ O)
    (hT : ∀ x : ℍ, x ∈ O → (1 : ℝ) +ᵥ x ∈ O → (2 : ℝ) +ᵥ x ∈ O → T2op f x = h₁ x)
    (hS : ∀ x : ℍ, ModularGroup.S • x ∈ O → ModularGroup.S • ((1 : ℝ) +ᵥ x) ∈ O →
      ModularGroup.S • ((2 : ℝ) +ᵥ x) ∈ O → S2op k f x = h₂ x)
    {γ δ : SL(2,ℤ)} (hδ : δ ∈ NeighborsP) {τ : ℍ} (hτ : τ ∈ O_F) (hδτ : δ • τ ∈ O_F) :
    (jFun δ (τ : ℂ)) ^ k * (∑ j : Fin 6, (sigmaHom (γ * δ)) 0 j * (slash k (MpElem j) f) τ)
      = (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (MpElem j) f) (δ • τ))
        - (jFun δ (τ : ℂ)) ^ k
            * (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (carryOdd₁ δ j) h₁) τ)
        - (jFun δ (τ : ℂ)) ^ k
            * (∑ j : Fin 6, (sigmaHom γ) 0 j * (slash k (carryOdd₂ δ j) h₂) τ) := by
  have hJ : (jFun δ (τ : ℂ)) ^ k ≠ 0 := zpow_ne_zero _ (jFun_ne_zero δ τ)
  have hsig : (∑ j : Fin 6, (sigmaHom (γ * δ)) 0 j * (slash k (MpElem j) f) τ)
      = ∑ p : Fin 6, (sigmaHom γ) 0 p
          * (∑ j : Fin 6, (sigmaHom δ) p j * (slash k (MpElem j) f) τ) := by
    simp only [sigmaHom_mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring))
  have hrow : ∀ i : Fin 6, (∑ j : Fin 6, (sigmaHom δ) i j * (slash k (MpElem j) f) τ)
      = slash k (MpElem i * ofSL δ) f τ
        - ((slash k (carryOdd₁ δ i) h₁) τ + (slash k (carryOdd₂ δ i) h₂) τ) := by
    intro i
    have h := small_extension_odd hk hMpO hT hS hδ hτ hδτ i
    simp only [smul_eq_mul] at h
    rw [← h]; ring
  have hstep3 : ∀ i : Fin 6, (jFun δ (τ : ℂ)) ^ k * (slash k (MpElem i * ofSL δ) f τ)
      = slash k (MpElem i) f (δ • τ) := by
    intro i
    have hmul : slash k (MpElem i * ofSL δ) f = slash k (ofSL δ) (slash k (MpElem i) f) := by
      rw [show MpElem i * ofSL δ = ofSL (Mp i) * ofSL δ from rfl,
        Work.Kernels.AlgebraFacts.slash_mul]
      rfl
    rw [hmul, slash_ofSL, Work.Kernels.slash_apply', _root_.zpow_neg, ← mul_assoc,
      mul_comm (jFun δ (τ : ℂ) ^ k), mul_assoc, mul_inv_cancel₀ hJ, mul_one]
  have hmain : ∀ i : Fin 6,
      (jFun δ (τ : ℂ)) ^ k * (∑ j : Fin 6, (sigmaHom δ) i j * (slash k (MpElem j) f) τ)
      = slash k (MpElem i) f (δ • τ) - (jFun δ (τ : ℂ)) ^ k
          * ((slash k (carryOdd₁ δ i) h₁) τ + (slash k (carryOdd₂ δ i) h₂) τ) := by
    intro i; rw [hrow i, mul_sub, hstep3 i]
  rw [hsig, Finset.mul_sum]
  rw [show (∑ p : Fin 6, (jFun δ (τ : ℂ)) ^ k * ((sigmaHom γ) 0 p
          * (∑ j : Fin 6, (sigmaHom δ) p j * (slash k (MpElem j) f) τ)))
      = ∑ p : Fin 6, (sigmaHom γ) 0 p
          * ((jFun δ (τ : ℂ)) ^ k * (∑ j : Fin 6, (sigmaHom δ) p j * (slash k (MpElem j) f) τ))
      from Finset.sum_congr rfl (fun p _ => by ring)]
  rw [show (∑ p : Fin 6, (sigmaHom γ) 0 p
          * ((jFun δ (τ : ℂ)) ^ k * (∑ j : Fin 6, (sigmaHom δ) p j * (slash k (MpElem j) f) τ)))
      = ∑ p : Fin 6, (sigmaHom γ) 0 p * (slash k (MpElem p) f (δ • τ)
          - (jFun δ (τ : ℂ)) ^ k
              * ((slash k (carryOdd₁ δ p) h₁) τ + (slash k (carryOdd₂ δ p) h₂) τ))
      from Finset.sum_congr rfl (fun p _ => by rw [hmain p])]
  rw [show (∑ p : Fin 6, (sigmaHom γ) 0 p * (slash k (MpElem p) f (δ • τ)
          - (jFun δ (τ : ℂ)) ^ k
              * ((slash k (carryOdd₁ δ p) h₁) τ + (slash k (carryOdd₂ δ p) h₂) τ)))
      = ∑ p : Fin 6, ((sigmaHom γ) 0 p * slash k (MpElem p) f (δ • τ)
          - (sigmaHom γ) 0 p * ((jFun δ (τ : ℂ)) ^ k
              * ((slash k (carryOdd₁ δ p) h₁) τ + (slash k (carryOdd₂ δ p) h₂) τ)))
      from Finset.sum_congr rfl (fun p _ => by ring)]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ p : Fin 6, (sigmaHom γ) 0 p * ((jFun δ (τ : ℂ)) ^ k
          * ((slash k (carryOdd₁ δ p) h₁) τ + (slash k (carryOdd₂ δ p) h₂) τ)))
      = (jFun δ (τ : ℂ)) ^ k * (∑ p : Fin 6, (sigmaHom γ) 0 p
          * ((slash k (carryOdd₁ δ p) h₁) τ + (slash k (carryOdd₂ δ p) h₂) τ))
      from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)]
  have hSsplit : (∑ p : Fin 6, (sigmaHom γ) 0 p
        * ((slash k (carryOdd₁ δ p) h₁) τ + (slash k (carryOdd₂ δ p) h₂) τ))
      = (∑ p : Fin 6, (sigmaHom γ) 0 p * (slash k (carryOdd₁ δ p) h₁) τ)
        + (∑ p : Fin 6, (sigmaHom γ) 0 p * (slash k (carryOdd₂ δ p) h₂) τ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hSsplit, mul_add]
  ring

/-! ## The transformation law for `Ψ` -/

/-- **The slash transformation law for `Ψ` at a neighbour.**  For a neighbour `δ` and
`τ ∈ O_F` with `δ • τ ∈ O_F`, the value of `Ψ(γδ, ·)` at `τ` is the value of `Ψ(γ, ·)` at
`δ • τ`, corrected by `j(δ,τ)^k`:

  `j(δ,τ)^k · Ψ(γδ, τ) = Ψ(γ, δτ)`.

This is `(★)` from the file header, and is the heart of the well-definedness of the extension
formula. -/
theorem Psi_mul_neighbor {k : ℤ} (hk : Odd k) {O O_F : Set ℍ} {f h₁ h₂ : ℍ → ℂ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Work.Asymptotics.Mp i) • τ ∈ O)
    (hT : ∀ x : ℍ, x ∈ O → (1 : ℝ) +ᵥ x ∈ O → (2 : ℝ) +ᵥ x ∈ O → T2op f x = h₁ x)
    (hS : ∀ x : ℍ, ModularGroup.S • x ∈ O → ModularGroup.S • ((1 : ℝ) +ᵥ x) ∈ O →
      ModularGroup.S • ((2 : ℝ) +ᵥ x) ∈ O → S2op k f x = h₂ x)
    {δ : SL(2,ℤ)} (hδ : δ ∈ NeighborsP) {τ : ℍ} (hτ : τ ∈ O_F) (hδτ : δ • τ ∈ O_F)
    (γ : SL(2,ℤ)) :
    (jFun δ (τ : ℂ)) ^ k * Psi k f h₁ h₂ (γ * δ) τ = Psi k f h₁ h₂ γ (δ • τ) := by
  have hsig := sigmaShift hk hMpO hT hS hδ hτ hδτ (γ := γ)
  have hc₁ := carryShift₁ hk γ δ h₁ τ
  have hc₂ := carryShift₂ hk γ δ h₂ τ
  simp only [Psi, smul_eq_mul]
  rw [mul_add, mul_add, hsig, hc₁, hc₂]
  ring

/-! ## Well-definedness -/

theorem Fodd_well_defined {k : ℤ} (hk : Odd k) {O O_F : Set UpperHalfPlane}
    {f h₁ h₂ : UpperHalfPlane → ℂ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Work.Asymptotics.Mp i) • τ ∈ O)
    (hT : ∀ x : UpperHalfPlane, x ∈ O → (1 : ℝ) +ᵥ x ∈ O → (2 : ℝ) +ᵥ x ∈ O →
      Work.Kernels.T2op f x = h₁ x)
    (hS : ∀ x : UpperHalfPlane, ModularGroup.S • x ∈ O → ModularGroup.S • ((1 : ℝ) +ᵥ x) ∈ O →
      ModularGroup.S • ((2 : ℝ) +ᵥ x) ∈ O → Work.Asymptotics.S2op k f x = h₂ x)
    (hNbd : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∃ τ : UpperHalfPlane, τ ∈ O_F ∧ γ • τ ∈ O_F) → γ ∈ Work.Asymptotics.NeighborsP)
    {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ} {τ τ' : UpperHalfPlane}
    (hτ : τ ∈ O_F) (hτ' : τ' ∈ O_F) (heq : γ • τ = γ' • τ') :
    Work.Kernels.jFun γ (τ : ℂ) ^ k * Work.Asymptotics.Psi k f h₁ h₂ γ τ
      = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * Work.Asymptotics.Psi k f h₁ h₂ γ' τ' := by
  -- the difference of the two presentations is a neighbour
  set δ : SL(2,ℤ) := γ⁻¹ * γ' with hδdef
  have hγ' : γ * δ = γ' := by rw [hδdef]; group
  have hδτ : δ • τ' = τ := by rw [hδdef, mul_smul, ← heq, inv_smul_smul]
  have hmem : δ • τ' ∈ O_F := by rw [hδτ]; exact hτ
  have hδN : δ ∈ NeighborsP := hNbd δ ⟨τ', hτ', hmem⟩
  have hkey := Psi_mul_neighbor hk hMpO hT hS hδN hτ' hmem γ
  rw [hγ', hδτ] at hkey
  -- the automorphy factors combine by multiplicativity
  have hjfun : jFun γ (τ : ℂ) * jFun δ (τ' : ℂ) = jFun γ' (τ' : ℂ) := by
    rw [← hδτ, ← jFun_mul, hγ']
  calc Work.Kernels.jFun γ (τ : ℂ) ^ k * Work.Asymptotics.Psi k f h₁ h₂ γ τ
      = Work.Kernels.jFun γ (τ : ℂ) ^ k
          * ((Work.Kernels.jFun δ (τ' : ℂ)) ^ k
              * Work.Asymptotics.Psi k f h₁ h₂ γ' τ') := by rw [← hkey]
    _ = (Work.Kernels.jFun γ (τ : ℂ) * Work.Kernels.jFun δ (τ' : ℂ)) ^ k
          * Work.Asymptotics.Psi k f h₁ h₂ γ' τ' := by rw [mul_zpow]; ring
    _ = Work.Kernels.jFun γ' (τ' : ℂ) ^ k
          * Work.Asymptotics.Psi k f h₁ h₂ γ' τ' := by rw [hjfun]

end Work.Asymptotics
