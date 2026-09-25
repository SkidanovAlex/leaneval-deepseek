import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.RankTheoryDeep.All
import Submission.NK.NUV2.ideleLeopoldt_two_of_halves
import Submission.NK.NUV2.ideleDualRank_finrank_lowerBound
import Submission.NK.NUV2.ideleDefectMono_attempt

/-!
# `NK.NUV2.ideleLeopoldt_two` — the idèle-side rank formula at `ℓ = 2`

**The target.**  `∃ δ : IntermediateField ℚ Ω → ℕ`, monotone in `K`, with

`Module.finrank (PadicInt 2) (Dual (C_K) 2) = r_ℂ(K) + 1 + δ K`

for every number field `K ⊆ Ω`, where `C_K = 𝕀_K ⧸ Kˣ` is the idèle class group and
`Dual (C_K) 2 = Hom_cts(C_K, ℤ_2)` its continuous character module.  This is the idèle-side half of
CoNF Ch. X §10.3, (10.3.20) `r_2(K) = r_ℂ(K) + 1 + δ_2(K)` together with the monotonicity of the
defect (10.3.7) Corollary.  It needs **no** class field theory: the arithmetic is local.

## Equivalent form, and why the two halves suffice

The formula *pins* `δ K = Module.finrank (Dual (C_K) 2) - (r_ℂ(K) + 1)`, so the target is
equivalent to the conjunction of

* **(lower bound)** `r_ℂ(K) + 1 ≤ Module.finrank (Dual (C_K) 2)` for every number field `K ⊆ Ω`; and
* **(monotonicity)** `Module.finrank (Dual (C_K) 2) - r_ℂ(K)` is monotone in `K`,

the truncated subtraction being exact by the lower bound.  Both are being formalised by the fleet:

* the lower bound is `NUV2/ideleDualRank_lowerBound`, from the **sharp local unit structure**
  `rank_{ℤ_2} Hom_cts(𝒪_qˣ, ℤ_2) = e_q f_q` at the places `q | 2` — its `≤` half is
  `NUV2/localUnits_two` (via the `2`-adic `exp`/`log` and the Frattini cover
  `NUV2/{ballCover_two,unitCover_two,rank_dual_le_of_cover}`), its `≥` half is
  `NUV2/localUnitDualRank_lowerBound` — together with the finiteness/upper bound
  `rank Hom_cts(C_K, ℤ_2) ≤ [K : ℚ]` of `NK.RankTheoryDeep.rank_dual_integralIdeles_le` and
  `NK.RankTheoryDeep.sum_localDeg_eq_finrank`;
* the monotonicity is the Leopoldt defect monotonicity CoNF (10.3.7) Cor. (conjecturally the
  content of Shimizu's Lemma 4f.2), delegated to `NUV2/ideleDefectMono_attempt`.

The underlying rank computation (the exact value `r_2(K) = r_ℂ(K) + 1 + δ_2(K)`, an equivalent
interface) is delegated to `NUV2/ideleRankFormula_attempt`.

## The mathematics of the monotonicity (the route to be formalised)

Let `u(K)` be the `ℤ_2`-rank of the `2`-adic closure `ℰ_K` of the diagonal image of `𝒪_Kˣ` in
`∏_{q | 2} 𝒪_qˣ`; then `r_2(K) = [K : ℚ] - u(K)` and the defect is `δ_2(K) = r(K) - u(K)` with
`r(K) = r_1(K) + r_2(K) - 1` the unit rank.  Equivalently, `δ_2(K)` is the `ℤ_2`-rank of the space
of `2`-adic *relations* `ker ( ℤ_2 ⊗ 𝒪_Kˣ → ℤ_2 ⊗ lim_n (𝒪_K ⧸ 2^n)ˣ )`.  For `K ⊆ L` the base
change `𝒪_K → 𝒪_L` carries relations of `K` to relations of `L` and is injective on the source
(the `2`-primary torsion is the roots of unity, which embed), so `δ_2(K) ≤ δ_2(L)`: the
monotonicity.  This is the `ℓ`-adic *flatness*/regulator argument, and it is the one piece of
CoNF (10.3.7) that has to be built here.
-/

namespace NK.NUV2

theorem ideleLeopoldt_two (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    ∃ δ : IntermediateField ℚ Ω → ℕ,
      (∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N → δ M ≤ δ N) ∧
        ∀ (K : IntermediateField ℚ Ω) [NumberField ↥K],
          Module.finrank (PadicInt 2)
              (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥K) 2)
            = NK.Reconstruct.rComplex ↥K + 1 + δ K :=
  NK.NUV2.ideleLeopoldt_two_of_halves Ω
    (fun K => NK.NUV2.ideleDualRank_finrank_lowerBound ↥K)
    (fun M N => NK.NUV2.ideleDefectMono_attempt Ω M N)

end NK.NUV2
