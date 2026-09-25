import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_increment_sum_le

/-!
# The *weighted* form of MST's input `(C2)`

Mirek–Stein–Trojan's Theorem 7 replaces the β-dependent Gauss sum by the *global* Weyl sum and then
applies the Rademacher–Menshov/sup-to-blocks inequality, which produces the *signed lacunary
combination of profile increments*

  `Θ_ε = Σ_{j<M} ε_j (Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}})`

(`mstThetaEps`).  MST invoke the theory of continuous singular Radon transforms
(`[bigs, Section 11]`, Duoandikoetxea–Rubio de Francia) for the fact that `Θ_ε` defines a bounded
operator on `L^r(ℝ)`, uniformly in the signs `ε` and in the number of terms `M`.

Their *Theorem 3* — the Ionescu–Wainger type theorem they actually apply — is stated with a
**weight**: for any multiplier `Θ` on `ℝ` with `‖·‖_{M_{2r}} ≤ A_{2r}`, the *periodic* multiplier

  `Δ_N(ξ) = Σ_{a/q ∈ 𝒰_N} Θ(ξ − a/q) η_N(ξ − a/q)`

satisfies `‖F^{-1}(Δ_N f̂)‖_{ℓ^p} ≤ C_{ρ,p} A_{2r} (log N) ‖f‖_{ℓ^p}`.  In the corpus's language the
weighted input is therefore the statement that **the `Θ_ε`-multiplier may be composed with any
circle symbol which is itself an `L^{2r}(ℝ)`-multiplier**, with the product of the constants; with
`Ψ` the level bump `mstEta d χ η s` this is exactly the hypothesis of the MST §5 estimate.

`MSTThetaWeightedMult P r A` below is that input, in the shape in which the assembly
`Maximal/mst_theta_bound` consumes it: `A` is the uniform multiplier norm of `Θ_ε`
(`i, M, ε` arbitrary with `‖ε j‖ ≤ 1`), and it composes on the right with any `IWMult r Ψ B`,
the product having norm `≤ A·B`.  The second conjunct is the conjugate-symbol version, needed
because `MSTThetaBound` demands the bound for both `mstThetaSym` and its conjugate.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The weighted form of MST's `(C2)`.**  For a fixed integer polynomial `P` and exponent `r`, the
signed lacunary profile-difference multiplier `Θ_ε = mstThetaEps P i M ε` — read on the circle
through the canonical lift `iwRep` — is an `L^{2r}(ℝ)`-multiplier with norm `≤ A`, uniformly in the
level `i`, the number of terms `M` and the signs `ε` with `‖ε j‖ ≤ 1`; and it may be composed with
any circle symbol `Ψ` which is an `L^{2r}(ℝ)`-multiplier of norm `≤ B`, the product having norm
`≤ A·B`.  The second conjunct is the same statement for the conjugate symbol
`ξ ↦ star (Θ_ε (iwRep ξ))`, again composed with an arbitrary `Ψ`.

Mathematically this is MST's Theorem 3 (the Ionescu–Wainger type theorem, with a general weight
`Θ` of multiplier norm `A`), specialised to the weight `Θ = Θ_ε`, together with the cited
uniform-in-signs `L^r`-boundedness of `Θ_ε` (continuous singular Radon transforms). -/
def MSTThetaWeightedMult (P : Polynomial ℤ) (r : ℕ) (A : ℝ) : Prop :=
  (∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) →
      ∀ (Ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (B : ℝ), 0 ≤ B → IWMult r Ψ B →
        IWMult r (fun ξ => mstThetaEps P i M ε (iwRep ξ) * Ψ ξ) (A * B)) ∧
  (∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) →
      ∀ (Ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (B : ℝ), 0 ≤ B → IWMult r Ψ B →
        IWMult r (fun ξ => star (mstThetaEps P i M ε (iwRep ξ)) * Ψ ξ) (A * B))

/-- **The raw (unweighted) form of MST's `(C2)`**: the signed lacunary profile-difference symbol
`Θ_ε = mstThetaEps P i M ε`, read on the circle through the canonical lift `iwRep`, is an
`L^{2r}(ℝ)`-multiplier with norm `≤ A`, uniformly in the level `i`, the number of terms `M` and the
signs `ε` with `‖ε j‖ ≤ 1`; and likewise for the conjugate symbol `ξ ↦ star (Θ_ε (iwRep ξ))`.

This is the citation of MST ([bigs, Section 11], Duoandikoetxea–Rubio de Francia): `Θ_ε` is a
continuous singular Radon transform, hence bounded on `L^r(ℝ)` uniformly in the signs. -/
def MSTThetaRawMult (P : Polynomial ℤ) (r : ℕ) (A : ℝ) : Prop :=
  ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) →
    IWMult r (fun ξ => mstThetaEps P i M ε (iwRep ξ)) A ∧
    IWMult r (fun ξ => star (mstThetaEps P i M ε (iwRep ξ))) A

/-! ## The uniform boundedness of `Θ_ε`

The block increments of `Θ_ε` are sums of *consecutive* profile increments, and the profile has
bounded dyadic variation uniformly in the frequency (`polyProfile_increment_sum_le`).  Hence the
signed lacunary combination is bounded by a constant depending only on `P` — *uniformly in the level
`i`, the number of terms `M` and the signs* `ε` (with `‖ε j‖ ≤ 1`).  This is the elementary structural
fact behind the whole chapter: `Θ_ε` is an `L^∞` symbol, so all the difficulty of MST's `(C2)` is in
the *multiplier* norm, not in the pointwise size.
-/

/-- The `j`-th block increment of `Θ_ε` telescopes into the consecutive profile increments. -/
lemma mstThetaEps_block_telescope (P : Polynomial ℤ) (i : ℕ) (θ : ℝ) (j : ℕ) :
    polyProfile P (2 ^ (j * 2 ^ i + 2 ^ i)) θ - polyProfile P (2 ^ (j * 2 ^ i)) θ
      = ∑ m ∈ Finset.Ico (j * 2 ^ i) (j * 2 ^ i + 2 ^ i),
          (polyProfile P (2 ^ (m + 1)) θ - polyProfile P (2 ^ m) θ) :=
  (Finset.sum_Ico_sub (fun m : ℕ => polyProfile P (2 ^ m) θ) (Nat.le_add_right _ _)).symm

/-- The blocks `Ico (j·2^i) (j·2^i + 2^i)`, `j < M`, tile `range (M·2^i)`. -/
lemma sum_range_blocks_eq (a : ℕ → ℝ) (M i : ℕ) :
    (∑ j ∈ Finset.range M, ∑ m ∈ Finset.Ico (j * 2 ^ i) (j * 2 ^ i + 2 ^ i), a m)
      = ∑ m ∈ Finset.range (M * 2 ^ i), a m := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_add_sum_Ico _ (Nat.le_add_right _ _)]
      simp [Nat.succ_mul]

/-- **`Θ_ε` is bounded uniformly in the level, the number of terms and the signs.** -/
theorem norm_mstThetaEps_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) →
      ∀ θ : ℝ, ‖mstThetaEps P i M ε θ‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := polyProfile_increment_sum_le P hc hd
  refine ⟨C, hCpos, ?_⟩
  intro i M ε hε θ
  have hterm : ∀ j : ℕ, ‖ε j * (polyProfile P (2 ^ ((j + 1) * 2 ^ i)) θ
      - polyProfile P (2 ^ (j * 2 ^ i)) θ)‖
      ≤ ∑ m ∈ Finset.Ico (j * 2 ^ i) (j * 2 ^ i + 2 ^ i),
          ‖polyProfile P (2 ^ (m + 1)) θ - polyProfile P (2 ^ m) θ‖ := by
    intro j
    have hexp : (j + 1) * 2 ^ i = j * 2 ^ i + 2 ^ i := by simp [Nat.succ_mul]
    rw [norm_mul, hexp, mstThetaEps_block_telescope P i θ j]
    calc ‖ε j‖ * ‖∑ m ∈ Finset.Ico (j * 2 ^ i) (j * 2 ^ i + 2 ^ i),
            (polyProfile P (2 ^ (m + 1)) θ - polyProfile P (2 ^ m) θ)‖
        ≤ 1 * ‖∑ m ∈ Finset.Ico (j * 2 ^ i) (j * 2 ^ i + 2 ^ i),
            (polyProfile P (2 ^ (m + 1)) θ - polyProfile P (2 ^ m) θ)‖ :=
          mul_le_mul_of_nonneg_right (hε j) (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ _ := norm_sum_le _ _
  calc ‖mstThetaEps P i M ε θ‖
      = ‖∑ j ∈ Finset.range M, ε j * (polyProfile P (2 ^ ((j + 1) * 2 ^ i)) θ
          - polyProfile P (2 ^ (j * 2 ^ i)) θ)‖ := by rw [mstThetaEps_apply]
    _ ≤ ∑ j ∈ Finset.range M, ‖ε j * (polyProfile P (2 ^ ((j + 1) * 2 ^ i)) θ
          - polyProfile P (2 ^ (j * 2 ^ i)) θ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range M, ∑ m ∈ Finset.Ico (j * 2 ^ i) (j * 2 ^ i + 2 ^ i),
          ‖polyProfile P (2 ^ (m + 1)) θ - polyProfile P (2 ^ m) θ‖ :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = ∑ m ∈ Finset.range (M * 2 ^ i),
          ‖polyProfile P (2 ^ (m + 1)) θ - polyProfile P (2 ^ m) θ‖ :=
        sum_range_blocks_eq _ M i
    _ ≤ C := hC θ (M * 2 ^ i)

end

end Work.BourgainPlan.Maximal
