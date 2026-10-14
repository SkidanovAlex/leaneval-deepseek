import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarP
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.wlInf_divz_slotsB
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.SliceWrapP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


/-- **The slicewise weighted bound, projected form**: a single constant `C` (depending only on the
mollifier) with `|JfamP ρ ε g(τ)|_{ℋ^k}² ≤ C·|g(τ)|_{ℋ⁶}²` for every `α ∈ (0,1]`, `k ≤ 6`,
`0 < ε ≤ 1`. -/
theorem HkSq_JfamP_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ g : Fam, ∀ τ : ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ)) Quad) →
        MeasureTheory.LocallyIntegrable (logPull (slice g τ)) volume →
        Work.Spaces.HkMem α 6 (slice g τ) →
        Work.Spaces.HkSq α k (slice (JfamP ρ ε g) τ)
          ≤ C * Work.Spaces.HkSq α 6 (slice g τ) := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := HkSq_Jeps_le ρ hρ.moll
  obtain ⟨A, hApos, hA⟩ := PZeroAux.hkNorm_Pz_le
  refine ⟨A ^ 2 * Real.exp CJ, by positivity, ?_⟩
  intro α hα k hk ε hε hε1 g τ hsm hloc hmem6
  have hmem6J : Work.Spaces.HkMem α 6 (Jeps ρ ε (slice g τ)) :=
    HkMem_Jeps hρ.moll hα hε hsm hmem6
  -- the `P₀`-distortion at level `k`
  have hP := hA α hα k hk (Jeps ρ ε (slice g τ))
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (Jeps_contDiffOn ρ hρ hε hloc)) hmem6J
  -- the `E1` bound at level `6`
  have hJ := hCJ α hα 6 ε hε hε1 (slice g τ) hsm hmem6 hmem6J
  have hsq : Work.Spaces.HkSq α k (slice (JfamP ρ ε g) τ)
      = (Work.Spaces.HkNorm α k (slice (JfamP ρ ε g) τ)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k _)]
  have hPz : slice (JfamP ρ ε g) τ = Pz (Jeps ρ ε (slice g τ)) := slice_JfamP ρ ε g τ
  rw [hsq, hPz]
  calc (Work.Spaces.HkNorm α k (Pz (Jeps ρ ε (slice g τ)))) ^ 2
      ≤ (A * Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g τ))) ^ 2 :=
        pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg _ _ _) hP 2
    _ = A ^ 2 * (Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g τ))) ^ 2 := by ring
    _ = A ^ 2 * Work.Spaces.HkSq α 6 (Jeps ρ ε (slice g τ)) := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)]
    _ ≤ A ^ 2 * (Real.exp (CJ * ε) * Work.Spaces.HkSq α 6 (slice g τ)) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ ≤ A ^ 2 * Real.exp CJ * Work.Spaces.HkSq α 6 (slice g τ) := by
        have hexp : Real.exp (CJ * ε) ≤ Real.exp CJ :=
          Real.exp_le_exp.mpr (by nlinarith [hCJpos, hε1])
        have h1 : A ^ 2 * Real.exp (CJ * ε) ≤ A ^ 2 * Real.exp CJ :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        calc A ^ 2 * (Real.exp (CJ * ε) * Work.Spaces.HkSq α 6 (slice g τ))
            = A ^ 2 * Real.exp (CJ * ε) * Work.Spaces.HkSq α 6 (slice g τ) := by ring
          _ ≤ A ^ 2 * Real.exp CJ * Work.Spaces.HkSq α 6 (slice g τ) :=
              mul_le_mul_of_nonneg_right h1 (Work.Spaces.HkSq_nonneg α 6 _)

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

set_option maxHeartbeats 1600000

/-! ## Auxiliary arithmetic

The three pieces `nsP0`, `nsP4`, `nsP8` are of the shape `c • (A · Q)` with `c = 2`, `-2`, `-2α`
and `(A, Q)` a "star coefficient × star slot" pair, so the flat-price star row `rowStarP` applies
to `A · Q` and the constant `c` is pulled out of the slot pairing (`SlotPairingConstMul`).

`rowStarP` produces the bound with the (good, sharp) `α^{-3}`-loss, the two star prices `KA`, `KQ`
and the datum price `M`; the target of the `N`-row only asks for the coarse
`α^{-10}(1+|Ce|+|Cs|)⁴(1+M)⁴`-form, so all that is left is the elementary arithmetic that the
star prices are `≤ (1+Cs·α)` resp. `≤ Cf·α` (i.e. are dominated by `1+|Ce|+|Cs|`) and that
`α^{-3} ≤ α^{-10}`, `1+M ≤ (1+M)⁴` for `0 < α ≤ 1`, `M ≥ 0`. -/

/-- Product monotonicity for four nonnegative factors. -/
private lemma four_le {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4)
    (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) :
    a1 * a2 * a3 * a4 ≤ b1 * b2 * b3 * b4 := by
  have h12 : a1 * a2 ≤ b1 * b2 := mul_le_mul h1 h2 ha2 hb1
  have h34 : a3 * a4 ≤ b3 * b4 := mul_le_mul h3 h4 ha4 hb3
  have h0 : 0 ≤ a3 * a4 := mul_nonneg ha3 ha4
  have hb : 0 ≤ b1 * b2 := mul_nonneg hb1 hb2
  calc a1 * a2 * a3 * a4 = (a1 * a2) * (a3 * a4) := by ring
    _ ≤ (b1 * b2) * (b3 * b4) := mul_le_mul h12 h34 h0 hb
    _ = b1 * b2 * b3 * b4 := by ring

/-- The coarse arithmetic of a single star × star-slot row: from the `rowStarP` output with the
star prices `KA ≤ Cst·(Cs·α)`, `KQ ≤ Cf·α` and `0 < α ≤ 1`, `Cs ≥ 0`, `M ≥ 0` one gets the
`α^{-10}(1+|Ce|+|Cs|)⁴(1+M)⁴`-form of the `N`-row. -/
private lemma arith {α C0 Cst Cf KA KQ M H Cs Ce X : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC0 : 0 ≤ C0) (hCst : 0 < Cst) (hCf : 0 < Cf) (hCs : 0 ≤ Cs)
    (hKA0 : 0 ≤ KA) (hKAle : KA ≤ Cst * (Cs * α))
    (hKQ0 : 0 ≤ KQ) (hKQle : KQ ≤ Cf * α)
    (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hX : X ≤ C0 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H)) :
    X ≤ C0 * (1 + Cst) * (1 + Cf) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        * (1 + H) := by
  set D : ℝ := 1 + |Ce| + |Cs| with hDdef
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    have h : (0 : ℝ) ≤ |Ce| + |Cs| := by positivity
    linarith
  have hCsD : 1 + Cs ≤ D := by
    have h : Cs ≤ |Cs| := le_abs_self Cs
    rw [hDdef]; linarith [abs_nonneg Ce]
  have hKA1 : 1 + KA ≤ (1 + Cst) * D := by
    have h1 : KA ≤ Cst * Cs := by
      refine le_trans hKAle ?_
      exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left hα1 hCs) hCst.le
    have h2 : 1 + Cst * Cs ≤ (1 + Cst) * (1 + Cs) := by nlinarith [hCst, hCs]
    have h3 : (1 + Cst) * (1 + Cs) ≤ (1 + Cst) * D :=
      mul_le_mul_of_nonneg_left hCsD (by linarith)
    linarith
  have hKQ1 : 1 + KQ ≤ (1 + Cf) * D := by
    have h1 : KQ ≤ Cf := le_trans hKQle (by simpa using mul_le_mul_of_nonneg_left hα1 hCf.le)
    have h2 : 1 + Cf ≤ (1 + Cf) * D := by nlinarith [hCf, hD1]
    linarith
  have hpow : α ^ (-(3 : ℝ)) ≤ α ^ (-(10 : ℝ)) := by
    have h7 : (1 : ℝ) ≤ α ^ (-(7 : ℝ)) := by
      rw [Real.rpow_neg hα0.le, ← Real.inv_rpow hα0.le]
      exact Real.one_le_rpow ((one_le_inv₀ hα0).mpr hα1) (by norm_num : (0 : ℝ) ≤ 7)
    have hadd : α ^ (-(10 : ℝ)) = α ^ (-(3 : ℝ)) * α ^ (-(7 : ℝ)) := by
      rw [← Real.rpow_add hα0]; norm_num
    rw [hadd]
    calc α ^ (-(3 : ℝ)) = α ^ (-(3 : ℝ)) * 1 := by ring
      _ ≤ α ^ (-(3 : ℝ)) * α ^ (-(7 : ℝ)) :=
          mul_le_mul_of_nonneg_left h7 (Real.rpow_nonneg hα0.le _)
  have hM1 : 0 ≤ 1 + M := by linarith
  have hH1 : 0 ≤ 1 + H := by linarith
  have hD2 : D ^ 2 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num : 2 ≤ 4)
  have hD24 : (1 + Cst) * (1 + Cf) * D ^ 2 ≤ (1 + Cst) * (1 + Cf) * D ^ 4 :=
    mul_le_mul_of_nonneg_left hD2 (by positivity)
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + M by linarith) (by norm_num : 1 ≤ 4)
    simpa using h
  have hAK : (1 + KA) * (1 + KQ) ≤ (1 + Cst) * (1 + Cf) * D ^ 4 :=
    le_trans (mul_le_mul hKA1 hKQ1 (by linarith) (by positivity)) (by
      calc ((1 + Cst) * D) * ((1 + Cf) * D) = (1 + Cst) * (1 + Cf) * D ^ 2 := by ring
        _ ≤ (1 + Cst) * (1 + Cf) * D ^ 4 := hD24)
  have h4 : (1 + M) * (1 + H) ≤ (1 + M) ^ 4 * (1 + H) :=
    mul_le_mul_of_nonneg_right hM4 hH1
  have key := four_le (le_refl C0) hpow hAK h4
    (Real.rpow_nonneg hα0.le _) (by positivity) (by positivity)
    hC0 (Real.rpow_nonneg hα0.le _) (by positivity)
  calc X ≤ C0 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := hX
    _ = C0 * α ^ (-(3 : ℝ)) * ((1 + KA) * (1 + KQ)) * ((1 + M) * (1 + H)) := by ring
    _ ≤ C0 * α ^ (-(10 : ℝ)) * ((1 + Cst) * (1 + Cf) * D ^ 4) * ((1 + M) ^ 4 * (1 + H)) := key
    _ = C0 * (1 + Cst) * (1 + Cf) * α ^ (-(10 : ℝ)) * D ^ 4 * (1 + M) ^ 4 * (1 + H) := by ring
    _ = C0 * (1 + Cst) * (1 + Cf) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + H) := by rw [← hDdef]

/-- **The flat-price "star coefficient × star slot" row.**

For a star coefficient `A` (one of `ℛ(Ξ₁)`, `𝒰(Ξ₁)/sin 2θ`, `𝒱(Ξ₁)`), a star slot `Q` (one of
`F_*`, `D_θF_*`, `D_zF_*`) and a constant factor `c` with `|c| ≤ 2`,

`|slotPairing ρ a b (c·(A·Q)) f| ≤ C α^{-10} (1+|Ce|+|Cs|)⁴ (1+M)⁴ (1+|f|²_{ℋ⁶})`

for every leaf weight `ρ` of the slot `a` (`a + b ≤ 6`) and every datum `f` with
`DatData α f M`.

This is the composition of `rowStarP` with the two datum lemmas `starDat` (the star prices, all
of them `≤ C·Cs·α` with the radial decay `z/(1+z)` and the angular gain `(α+σ)σ^{α/5}`) and
`fstarDat` (the star-slot prices, `≤ C·α` with the decay `z/(1+z)²` and the gain `σ^{α/3}`),
followed by `arith`.  The star prices are consumed through the *disjunctions* of `starDat` /
`fstarDat`, so no case analysis over the nine combinations survives into the caller. -/
private theorem starSlotRow (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (Φs f : Work.FTS.Galerkin.Fn) (Cs M c : ℝ),
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      |c| ≤ 2 →
      ∀ (A Q : Work.FTS.Galerkin.Fn),
        (A = Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) ∨
         A = (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
              / Work.Construction.s2 θ) ∨
         A = Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) →
        (Q = Work.Construction.Fstar α ∨
         Q = Work.Spaces.Dth (Work.Construction.Fstar α) ∨
         Q = Work.Spaces.Dz (Work.Construction.Fstar α)) →
        ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * (A z θ * Q z θ)) f|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C0, hC0, hrow⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarP
  obtain ⟨Cst, hCst, hstar⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat
  obtain ⟨Cf, hCf, hfst⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
  refine ⟨2 * C0 * (1 + Cst) * (1 + Cf), by positivity, ?_⟩
  intro α hα Φs f Cs M c hstar6 hdat hc A Q hA hQ a b ρ hab hleaf
  obtain ⟨hRsm, hUsm, hVsm, hstarP⟩ := hstar α hα Φs Cs hstar6
  obtain ⟨hFsm, hDTsm, hDZsm, -, -, -, -, -, -, hfstP⟩ := hfst α hα
  -- the star price forces `0 ≤ Cs` (evaluate the bound at `(z,θ) = (1,π/4)`)
  have hCs : 0 ≤ Cs := by
    have h := hstarP (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) (Or.inl rfl)
      0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
      if_neg (by norm_num : ¬ (1 : ℕ) ≤ 0), mul_one] at h
    have h2 : (0 : ℝ) ≤ Cst * (Cs * α) * (1 / (1 + 1)) := le_trans (abs_nonneg _) h
    have h3 : (0 : ℝ) < Cst * α := mul_pos hCst hα.1
    nlinarith [h2, h3]
  have hsmA : Work.FTS.EllipticEst.SmoothOpen A := by
    rcases hA with rfl | rfl | rfl
    · exact hRsm
    · exact hUsm
    · exact hVsm
  have hsmQ : Work.FTS.EllipticEst.SmoothOpen Q := by
    rcases hQ with rfl | rfl | rfl
    · exact hFsm
    · exact hDTsm
    · exact hDZsm
  have hAdec : ∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ (Cst * (Cs * α)) * (z / (1 + z)) *
        (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
    intro j i hji z θ hz hθ0 hθ1
    rcases hA with rfl | rfl | rfl
    · exact hstarP _ (Or.inl rfl) j i hji z θ hz hθ0 hθ1
    · exact hstarP _ (Or.inr (Or.inl rfl)) j i hji z θ hz hθ0 hθ1
    · exact hstarP _ (Or.inr (Or.inr rfl)) j i hji z θ hz hθ0 hθ1
  have hQdec : ∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i Q z θ| ≤ (Cf * α) * (z / (1 + z) ^ 2) *
        (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1) := by
    intro j i hji z θ hz hθ0 hθ1
    rcases hQ with rfl | rfl | rfl
    · exact hfstP _ (Or.inl rfl) j i hji z θ hz hθ0 hθ1
    · exact hfstP _ (Or.inr (Or.inl rfl)) j i hji z θ hz hθ0 hθ1
    · exact hfstP _ (Or.inr (Or.inr rfl)) j i hji z θ hz hθ0 hθ1
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hH0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hY := hrow α hα A Q f (Cst * (Cs * α)) (Cf * α) M a b ρ hsmA hsmQ hdat hAdec hQdec
    hab hleaf
  have hcp : Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * (A z θ * Q z θ)) f
      = c * Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Q z θ) f :=
    @Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingConstMul ρ a b c
      (fun z θ => A z θ * Q z θ) f
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.smoothOpen_mul hsmA hsmQ)
  rw [hcp, abs_mul]
  refine le_trans (mul_le_mul hc hY (abs_nonneg _) (by norm_num)) ?_
  rw [show 2 * (C0 * α ^ (-(3 : ℝ)) * (1 + Cst * (Cs * α)) * (1 + Cf * α) * (1 + M)
        * (1 + Work.Spaces.HkSq α 6 f))
      = (2 * C0) * α ^ (-(3 : ℝ)) * (1 + Cst * (Cs * α)) * (1 + Cf * α) * (1 + M)
        * (1 + Work.Spaces.HkSq α 6 f) from by ring]
  have hKA0 : 0 ≤ Cst * (Cs * α) := mul_nonneg hCst.le (mul_nonneg hCs hα.1.le)
  have hKQ0 : 0 ≤ Cf * α := mul_nonneg hCf.le hα.1.le
  exact arith hα.1 hα.2 (by positivity) hCst hCf hCs hKA0 (le_refl _)
    hKQ0 (le_refl _) hM0 hH0 (le_refl _)

/-- Piece bounds for the three "star coefficient × star slot" pieces of the level-six `N`-row:
`nsP0 = 2·Rop(PhiTs α Φs)·F_*`, `nsP4 = -2·(Uop(PhiTs α Φs)/s2)·D_θF_*`,
`nsP8 = -2α·Vop(PhiTs α Φs)·D_zF_*`.
Route: a pointwise-priced `A·Q` slot row (pointwise decay `z/(1+z)` for `A`, `z/(1+z)^2` for `Q`,
plus the angular gain `(α+σ)σ^{α/5}` resp. `σ^{α/3}` on the `1 ≤ i` slots) applied with
`starDat` (prices `≈ Cs·α`) and `fstarDat` (prices `≈ α`); the datum data is
`T6Coef.DatData α (slice g τ) M` from `L6Ctx` via `datData_of_H6Adm`. -/
theorem nsumG1 (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (|Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP0 α Φs) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP4 α Φs) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP8 α Φs) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))) := by
  obtain ⟨Cg, hCg, hG⟩ := starSlotRow Ce
  refine ⟨Cg, hCg, ?_⟩
  intro α hα g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  have hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs := hctx.hstar6
  have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α (Work.FTS.Galerkin.slice g τ) M :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd
  refine ⟨?_, ?_, ?_⟩
  · -- `nsP0 = 2·(ℛ(Ξ₁) · F_*)`
    have hfun : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP0 α Φs
        = fun z θ => (2 : ℝ) * (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            * Work.Construction.Fstar α z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP0,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefR1,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.slotFs]
      ring
    rw [hfun]
    exact hG α hα Φs (Work.FTS.Galerkin.slice g τ) Cs M 2 hstar6 hdat (by norm_num)
      (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) (Work.Construction.Fstar α)
      (Or.inl rfl) (Or.inl rfl) a b ρ hab hleaf
  · -- `nsP4 = -2·((𝒰(Ξ₁)/sin 2θ) · D_θF_*)`
    have hfun : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP4 α Φs
        = fun z θ => (-2 : ℝ) * ((Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP4,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefU1,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.slotTs]
      ring
    rw [hfun]
    exact hG α hα Φs (Work.FTS.Galerkin.slice g τ) Cs M (-2) hstar6 hdat (by norm_num)
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)
      (Work.Spaces.Dth (Work.Construction.Fstar α))
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) a b ρ hab hleaf
  · -- `nsP8 = -2α·(𝒱(Ξ₁) · D_zF_*)`
    have hc8 : |(-2 : ℝ) * α| ≤ 2 := by
      rw [abs_mul, abs_of_pos hα.1]
      have h2 : |(-2 : ℝ)| = 2 := by norm_num
      rw [h2]; linarith [hα.2]
    have hfun : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP8 α Φs
        = fun z θ => ((-2 : ℝ) * α) * (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP8,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefV1,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.slotZs]
      ring
    rw [hfun]
    exact hG α hα Φs (Work.FTS.Galerkin.slice g τ) Cs M (-2 * α) hstar6 hdat hc8
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs))
      (Work.Spaces.Dz (Work.Construction.Fstar α))
      (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) a b ρ hab hleaf

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
end
