import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.derH_derivation
import Submission.Work.BW.ellW_eq_rank
import Submission.Work.BW.card_weight_le
import Submission.Work.BW.applyL_compose
import Submission.Work.BW.applyL_pow_le
import Submission.Work.BW.exists_minor
import Submission.Work.BW.applyL_mem_span
import Submission.Work.BW.coheight_ge_of_indep
import Submission.Work.BW.uGen_facts
import Submission.Work.BW.extract_coeff
import Submission.Work.BW.indep_localization
import Submission.Work.BW.chiMat_rank
import Submission.Work.BW.minor_congruence
import Submission.Work.BW.indep_of_cong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Wüstholz's multiplicity estimate (Philippon 4.6–4.7)

Let `𝔓 = subIdeal N ρ ε M` be the ideal of the connected subgroup
`G' = G_a^ε × ker 𝒵 ⊂ G = G_a × G_m^N`, and let `ℓ = dim W − dim (W ∩ Lie G')` be the rank of
the matrix of linear forms cutting out `Lie G'` (the `ρ` character rows, plus the
`G_a`-coordinate when `ε = false`).  If `𝔓` is a minimal prime of `J` and every product of at
most `T` of the invariant derivations `derH (w k)` maps `J` into `𝔓`, then the primary component
of `J` at `𝔓` has length at least the number `C(T+ℓ,ℓ)` of monomials of degree `≤ T` in `ℓ`
variables.

The proof follows Philippon 4.6–4.7.  Since `derH w (χ^{M} - 1) ≡ (M · w) · χ^{M} - 1` and
`derH w (X₀₁) = w₀X₀₀` modulo `𝔓`, the matrix `A` of linear forms has rank `ℓ`
(`Work.BW.chiMat_rank`); an invertible `ℓ × ℓ` minor dualises it into derivations `Λ i` with
`Λ i (u j) ≡ D j δᵢⱼ` (`Work.BW.minor_congruence`).  The coefficient extraction
(`Work.BW.extract_coeff`) then shows that the degree-`τ` monomials in the `uᵢ` are independent
modulo `J + 𝔓^{τ+1}` (`Work.BW.indep_of_cong`), this passes to the local ring
(`Work.BW.indep_localization`), and the degree filtration gives the length bound
(`Work.BW.coheight_ge_of_indep`).
-/

namespace Work.BW

lemma applyH_zero {N' q' : ℕ} (w : Fin q' → Fin (N' + 1) → ℂ) (F : MR N') :
    applyH w 0 F = F := by
  unfold applyH
  induction (List.finRange q') with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldr_cons]
    simpa using ih

/-- The core of the argument: Wüstholz's length bound for the abstract matrix of linear forms. -/
theorem core {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (𝔓 : Ideal (MR N)) (hprime : 𝔓.IsPrime)
    (J : Ideal (MR N)) (hJ : 𝔓 ∈ J.minimalPrimes) (T : ℕ)
    (hT : ∀ F ∈ J, ∀ t : Fin q → ℕ, ∑ k, t k ≤ T → applyH w t F ∈ 𝔓)
    {ℓ n : ℕ} (A : Matrix (Fin n) (Fin q) ℂ) (u D : Fin n → MR N)
    (hrank : A.rank = ℓ) (hu : ∀ j, u j ∈ 𝔓) (hD : ∀ j, D j ∉ 𝔓)
    (hder : ∀ (j : Fin n) (k : Fin q), derH (w k) (u j) - A j k • D j ∈ 𝔓) :
    ((T + ℓ).choose ℓ : ℕ∞) ≤ primLen J 𝔓 := by
  classical
  haveI := hprime
  -- dualise the generators
  obtain ⟨Ji, Ki, c, hcong⟩ := minor_congruence w 𝔓 A u D hrank hder
  -- the independence of the monomials modulo `J + 𝔓^{τ+1}`
  have hindR := indep_of_cong w 𝔓 hprime J T hT (fun b => u (Ji b)) (fun b => D (Ji b)) c Ki
    (fun b => hu (Ji b)) (fun b => hD (Ji b)) hcong
  -- the target ideal of the localization is proper
  have h𝔓ne : Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) 𝔓 ≠ ⊤ := by
    intro htop
    have h1 : (1 : Localization 𝔓.primeCompl) ∈
        Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) 𝔓 := by
      rw [htop]; exact Submodule.mem_top
    rw [show (1 : Localization 𝔓.primeCompl)
        = algebraMap (MR N) (Localization 𝔓.primeCompl) 1 from (map_one _).symm] at h1
    obtain ⟨m, hm, hm1⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := 𝔓.primeCompl)
      (S := Localization 𝔓.primeCompl) 𝔓 1).mp h1
    exact hm (by simpa using hm1)
  -- clearing denominators
  have hindS : ∀ (τ : ℕ), τ ≤ T → ∀ C : (Fin ℓ → ℕ) → Localization 𝔓.primeCompl,
      (∑ β ∈ weightFinset ℓ τ, C β
          * monoPow (fun i => algebraMap (MR N) (Localization 𝔓.primeCompl) (u (Ji i))) β)
        ∈ Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) J
          + (Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) 𝔓) ^ (τ + 1) →
      ∀ α ∈ weightFinset ℓ τ,
        C α ∈ Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) 𝔓 := by
    intro τ hτ C hmem
    exact indep_localization (M := 𝔓.primeCompl) (S := Localization 𝔓.primeCompl) J 𝔓
      (fun b => u (Ji b)) τ (fun C' hC' => hindR τ hτ C' hC') C hmem
  -- the degree filtration
  have hco : (((T + ℓ).choose ℓ : ℕ) : ℕ∞)
      ≤ Order.coheight (Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) J) := by
    refine coheight_ge_of_indep (Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) J)
      (Ideal.map (algebraMap (MR N) (Localization 𝔓.primeCompl)) 𝔓)
      (fun i => algebraMap (MR N) (Localization 𝔓.primeCompl) (u (Ji i))) ?_ ?_ ?_ ?_
    · refine Ideal.map_mono ?_
      intro x hx
      simpa only [applyH_zero] using hT x hx 0 (by simp)
    · exact h𝔓ne
    · exact fun i => Ideal.mem_map_of_mem _ (hu (Ji i))
    · exact fun τ hτ C hmem => hindS τ hτ C hmem
  rw [primLen, dif_pos hprime, Module.length_quotient]
  exact hco

/-- B3b (Philippon 4.6–4.7, Wüstholz). If `I(G')` is a minimal prime of `J` and `δ^t J ⊆ I(G')`
for all `|t| ≤ T`, then the primary component of `J` at `I(G')` has length `≥ C(T + ℓ, ℓ)`,
`ℓ = dim W − dim (W ∩ Lie G')`. Proof: pick `u_j ∈ I(G')` (homogenised `χ^{M_j} − 1`, and `X₀₁`
if `ε = false`) and `ℓ` derivations in `W` with `δ_i u_j ≡ δ_{ij}` mod `I(G')` (4.6: the matrix
`(δ_{w_k} u_j)` is constant on `G'` of rank `ℓ`); for each `τ ≤ T` the monomials `u^α`, `|α| = τ`,
are independent over the residue field modulo `J + I(G')^{τ+1}` (apply `δ^{α}`); sum the graded
pieces of `(R/J)_{I(G')}`. Size 2.5–4k. -/
theorem wuestholz_length {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) (J : Ideal (MR N))
    (hJ : subIdeal N ρ ε M ∈ J.minimalPrimes) (T : ℕ)
    (hT : ∀ F ∈ J, ∀ t : Fin q → ℕ, ∑ k, t k ≤ T → applyH w t F ∈ subIdeal N ρ ε M) :
    (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℕ∞) ≤ primLen J (subIdeal N ρ ε M) := by
  cases ε with
  | false =>
    obtain ⟨-, hrank⟩ := chiMat_rank w M
    exact core (w := w) (𝔓 := subIdeal N ρ false M) hJ.1.1 (J := J) hJ T hT
      (A := chiMat w M false) (u := fun j => uGen M false (uIdxEmb (ε := false) j))
      (D := fun j => chiMon M false (uIdxEmb (ε := false) j)) hrank
      (fun j => (uGen_facts M false).2.1 (uIdxEmb (ε := false) j))
      (fun j => (uGen_facts M false).2.2.1 (uIdxEmb (ε := false) j) (Or.inr rfl))
      (fun j k => (uGen_facts M false).1 (uIdxEmb (ε := false) j) (w k))
  | true =>
    obtain ⟨hrank, -⟩ := chiMat_rank w M
    exact core (w := w) (𝔓 := subIdeal N ρ true M) hJ.1.1 (J := J) hJ T hT
      (A := chiMat w M true) (u := fun j => uGen M true (uIdxEmb (ε := true) j))
      (D := fun j => chiMon M true (uIdxEmb (ε := true) j)) hrank
      (fun j => (uGen_facts M true).2.1 (uIdxEmb (ε := true) j))
      (fun j => (uGen_facts M true).2.2.1 (uIdxEmb (ε := true) j) (Or.inl j.isLt))
      (fun j k => (uGen_facts M true).1 (uIdxEmb (ε := true) j) (w k))

end Work.BW
