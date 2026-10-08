import Mathlib
import Submission.Work.BG.glauberman_two_setup
import Submission.Work.BG.glauberman_two_coset_sum
import Submission.Work.BG.glauberman_two_eigenspace
import Submission.Work.BG.glauberman_two_extension

/-!
# Glauberman's theorem for an automorphism of order two

`Work.BG.glauberman_two`: for a finite group `U` of odd order, an involutive automorphism
`σ` of `U` and a `σ`-invariant irreducible character `α` of `U`, the restriction of `α` to
the fixed-point subgroup `C_U(σ)` has a unique irreducible constituent of odd multiplicity.

This is the `|A| = 2` case of Glauberman's character correspondence
(G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
Canad. J. Math. **20** (1968), 1365-1488, Theorem 3 and Corollary 4), in the form used by
Bender-Glauberman, *Characters of finite groups with dihedral Sylow 2-subgroups*,
J. Algebra **70** (1981), Lemma 1.9.

The proof follows Glauberman's argument: the `σ`-invariant `α` extends to an irreducible
character `η` of the semidirect product `Γ = U ⋊ ⟨σ⟩` (`glauberman_two_extension`); on the
two `σ`-eigenspaces of the representation affording `η` one gets two genuine characters
`ν⁺`, `ν⁻` of `C_U(σ)` with `η|_{C_U(σ)} = ν⁺ + ν⁻` and `η(a·−) = ν⁺ − ν⁻`
(`glauberman_two_eigenspace`, a linear-algebra computation); the coset sum identity
`Σ_{u ∈ U} μ(au) = [U : C_U(σ)] Σ_{b ∈ C_U(σ)} μ(ab)` for class functions `μ` on `Γ`
(`glauberman_two_coset_sum`, Glauberman's Lemma 2) turns the elementary identity
`Σ_{u ∈ U} ‖η(au)‖² = |U|` into `‖ν⁺ − ν⁻‖² = 1`; expanding `ν⁺ − ν⁻` in the irreducible
characters of `C_U(σ)` then gives that exactly one multiplicity is odd.

## Files

* `Submission/Work/BG/glauberman_two_setup.lean` — the semidirect product `Γ = U ⋊ ⟨σ⟩`, its
  involution `a = Gam.gInv σ`, the inclusion `Gam.iot` and their elementary API (author: this
  task).
* `Submission/Work/BG/glauberman_two_extension.lean`, `..._eigenspace.lean`,
  `..._coset_sum.lean` — the three building blocks quoted above, each proved in its own file.
* `Submission/Work/BG/glauberman_two_aux_coset_rep.lean`, `..._aux_coset_conj.lean`,
  `..._aux_centralizer.lean` — the class-correspondence facts of Glauberman's Lemma 2 in the
  case `|A| = 2` (surjectivity onto `C_U(σ)`, the conjugacy criterion, the centralizer
  `C_Γ(a·t) = ⟨a⟩·C_{C_U(σ)}(t)`); these are independent of, and not needed by, the proof
  below (which uses `..._coset_sum` instead), but record the group theory for area `BG`.
* Development scaffolds left in place (not part of any library): the root-level Lean files
  `_gw2_stmt_check.lean`, `_gw2_aux_stmt.lean`, `_gw2_axcheck.lean`, `_gw2_ax2.lean`
  (statement elaboration checks) and the GAP scripts `_mytest*.g`, `_testconj.g`,
  `_sdtest.g` (numerical verification of the identity `‖ν⁺ − ν⁻‖² = 1` and of the
  class-correspondence counts on all small odd-order groups).
-/

namespace Work.BG

open scoped BigOperators
open OddOrder.RepresentationTheory

/-- Integer arithmetic: `(m - n)^2 = 1` forces `m + n = 2 * min m n + 1`. -/
theorem gw2_int_add_eq_two_mul_min_add_one {m n : ℤ} (h : (m - n) ^ 2 = 1) :
    m + n = 2 * min m n + 1 := by
  have hfac : (m - n - 1) * (m - n + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h' | h'
  · have hmn : m = n + 1 := by omega
    have hmin : min (n + 1) n = n := min_eq_right (by omega)
    omega
  · have hmn : m = n - 1 := by omega
    have hmin : min (n - 1) n = n - 1 := min_eq_left (by omega)
    omega

/-- Integer arithmetic: if `m + n = 2k + 1` then `m ≠ n`. -/
theorem gw2_int_sub_ne_zero_of_add_eq_two_mul_add_one {m n k : ℤ} (h : m + n = 2 * k + 1) :
    m - n ≠ 0 := by
  intro h0
  omega

/-- Integer arithmetic: `(m - n)^2 = 1` exhibits `m + n` as `2k + 1`. -/
theorem gw2_int_add_eq_two_mul_add_one_of_sq {m n : ℤ} (h : (m - n) ^ 2 = 1) :
    ∃ k : ℤ, m + n = 2 * k + 1 :=
  ⟨min m n, gw2_int_add_eq_two_mul_min_add_one h⟩


/-- Parseval for an orthogonal family of irreducible characters. -/
theorem gw2_inner_self_sum_smul {H : Type*} [Group H] [Fintype H]
    [Fintype (IrreducibleCharacter H)] [Invertible (Nat.card H : ℂ)]
    (a : IrreducibleCharacter H → ℂ) :
    ClassFunction.inner (∑ χ : IrreducibleCharacter H, a χ • (χ : ClassFunction H ℂ))
        (∑ χ : IrreducibleCharacter H, a χ • (χ : ClassFunction H ℂ)) =
      ∑ χ : IrreducibleCharacter H, a χ * star (a χ) := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [ClassFunction.inner_smul_right]
  have hsingle : ClassFunction.inner (∑ ψ : IrreducibleCharacter H,
      a ψ • (ψ : ClassFunction H ℂ)) (χ : ClassFunction H ℂ) = a χ := by
    rw [inner_sum_left, Finset.sum_eq_single χ]
    · rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, ite_eq_left rfl,
        mul_one]
    · intro ψ _ hψ
      rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, ite_eq_right hψ,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ χ) h
  rw [hsingle]
  ring

/-- Parseval identity for the Fourier expansion of a class function. -/
theorem gw2_inner_self_eq_sum_inner_mul_star {H : Type*} [Group H] [Fintype H]
    [Fintype (IrreducibleCharacter H)] [Invertible (Nat.card H : ℂ)]
    (f : ClassFunction H ℂ) :
    ClassFunction.inner f f = ∑ χ : IrreducibleCharacter H,
      ClassFunction.inner f (χ : ClassFunction H ℂ) *
        star (ClassFunction.inner f (χ : ClassFunction H ℂ)) := by
  have h := gw2_inner_self_sum_smul (H := H)
    (a := fun χ => ClassFunction.inner f (χ : ClassFunction H ℂ))
  rwa [sum_inner_irreducibleCharacter_smul f] at h

theorem glauberman_two {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(Work.BG.fixedSubgroup σ)] [Invertible (Nat.card ↥(Work.BG.fixedSubgroup σ) : ℂ)]
    (α : OddOrder.RepresentationTheory.IrreducibleCharacter U)
    (hα : ∀ u : U, (α : OddOrder.RepresentationTheory.ClassFunction U ℂ) (σ u) =
      (α : OddOrder.RepresentationTheory.ClassFunction U ℂ) u) :
    ∃! β : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.BG.fixedSubgroup σ),
      ∃ k : ℤ, OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.BG.fixedSubgroup σ)
          (α : OddOrder.RepresentationTheory.ClassFunction U ℂ))
        (β : OddOrder.RepresentationTheory.ClassFunction ↥(Work.BG.fixedSubgroup σ) ℂ)
        = (2 * k + 1 : ℂ) := by
  classical
  haveI : Fintype (IrreducibleCharacter ↥(fixedSubgroup σ)) := Fintype.ofFinite _
  -- ### Step 1: an extension `η` of `α` to `Γ = U ⋊ ⟨σ⟩`
  obtain ⟨η, hηirr, hηres, hηnorm⟩ := glauberman_two_extension (σ := σ) hσ α hα
  -- ### Step 2: a representation affording `η`
  obtain ⟨V, hVadd, hVmod, hVfd, ρ, hρirr, hρη⟩ := hηirr
  letI hVI1 : AddCommGroup V := hVadd
  letI hVI2 : Module ℂ V := hVmod
  letI hVI3 : FiniteDimensional ℂ V := hVfd
  -- ### Step 3: the ±1 eigenspace decomposition of `V` under `a = gInv σ`
  obtain ⟨νp, νm, hνp, hνm, hνsum, hνdiff⟩ :=
    @glauberman_two_eigenspace U _ σ hσ V hVadd hVmod hVfd ρ
  -- ### Step 4: the norm-square class function and the coset sum identity
  let μ : ClassFunction (Gam σ) ℂ :=
    ⟨fun g => η g * star (η g), by
      intro g h
      show η (h * g * h⁻¹) * star (η (h * g * h⁻¹)) = η g * star (η g)
      rw [ClassFunction.conj_eq η g h]⟩
  have hμpt : ∀ x : Gam σ, μ x = ((‖η x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    show η x * star (η x) = ((‖η x‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hμsum : ∑ u : U, μ (Gam.gInv σ * Gam.iot σ u) = (Nat.card U : ℂ) := by
    rw [Finset.sum_congr rfl (fun u _ => hμpt _)]
    have hcast : ((∑ u : U, ‖η (Gam.gInv σ * Gam.iot σ u)‖ ^ 2 : ℝ) : ℂ) =
        ∑ u : U, ((‖η (Gam.gInv σ * Gam.iot σ u)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [← hcast, hηnorm]
    norm_num
  have hUnz : ((Nat.card U : ℂ)) ≠ 0 := by
    have hne : Nat.card U ≠ 0 := by
      rintro h0
      obtain ⟨k, hk⟩ := hU
      omega
    exact_mod_cast hne
  have hBsum : ∑ b : ↥(fixedSubgroup σ), μ (Gam.gInv σ * Gam.iot σ (b : U)) =
      (Nat.card ↥(fixedSubgroup σ) : ℂ) := by
    have hcoset := glauberman_two_coset_sum (U := U) (hU := hU) (σ := σ) (hσ := hσ) μ
    rw [hμsum] at hcoset
    have h2 : (Nat.card ↥(fixedSubgroup σ) : ℂ) =
        ∑ b : ↥(fixedSubgroup σ), μ (Gam.gInv σ * Gam.iot σ (b : U)) := by
      rw [mul_comm] at hcoset
      exact mul_left_cancel₀ hUnz hcoset
    exact h2.symm
  -- ### Step 5: `⟨νp - νm, νp - νm⟩ = 1`
  have hnorm : ClassFunction.inner (νp - νm) (νp - νm) = 1 := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
    have hstep : (∑ b : ↥(fixedSubgroup σ), (νp - νm) b * star ((νp - νm) b)) =
        ∑ b : ↥(fixedSubgroup σ), μ (Gam.gInv σ * Gam.iot σ (b : U)) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      have h1 : (νp - νm) b = ρ.character (Gam.gInv σ * Gam.iot σ (b : U)) := by
        rw [ClassFunction.sub_apply, hνdiff b]
      have h2 : η (Gam.gInv σ * Gam.iot σ (b : U)) = (νp - νm) b := by
        rw [congrFun hρη (Gam.gInv σ * Gam.iot σ (b : U)), h1]
      rw [← h2]
    rw [hstep, hBsum, invOf_mul_self]
  -- ### Step 6: integrality of the multiplicities of `νp`, `νm`
  have hc : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ), ∃ m : ℤ,
      ClassFunction.inner νp (β : ClassFunction ↥(fixedSubgroup σ) ℂ) = (m : ℂ) :=
    fun β => mem_ZIrr_inner_int β (IsCharacter.mem_ZIrr hνp)
  have hd : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ), ∃ m : ℤ,
      ClassFunction.inner νm (β : ClassFunction ↥(fixedSubgroup σ) ℂ) = (m : ℂ) :=
    fun β => mem_ZIrr_inner_int β (IsCharacter.mem_ZIrr hνm)
  choose c hc' using hc
  choose d hd' using hd
  -- ### Step 7: `∑ (c β - d β)^2 = 1`
  have hparsC : ∑ β : IrreducibleCharacter ↥(fixedSubgroup σ), ((c β - d β : ℤ) : ℂ) ^ 2 = 1 := by
    have hf : ClassFunction.inner (νp - νm) (νp - νm) =
        ∑ β : IrreducibleCharacter ↥(fixedSubgroup σ), ((c β - d β : ℤ) : ℂ) ^ 2 := by
      rw [gw2_inner_self_eq_sum_inner_mul_star (νp - νm)]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      have hcoeff : ClassFunction.inner (νp - νm) (β : ClassFunction ↥(fixedSubgroup σ) ℂ)
          = ((c β - d β : ℤ) : ℂ) := by
        rw [ClassFunction.inner_sub_left, hc' β, hd' β]
        push_cast
        ring
      rw [hcoeff, star_intCast]
      ring
    rw [hf] at hnorm
    exact hnorm
  have hparsZ : ∑ β : IrreducibleCharacter ↥(fixedSubgroup σ), (c β - d β) ^ 2 = 1 := by
    have hcast : ((∑ β : IrreducibleCharacter ↥(fixedSubgroup σ), (c β - d β) ^ 2 : ℤ) : ℂ) =
        ∑ β : IrreducibleCharacter ↥(fixedSubgroup σ), ((c β - d β : ℤ) : ℂ) ^ 2 := by
      push_cast
      refine Finset.sum_congr rfl (fun β _ => ?_)
      ring
    have h : ((∑ β : IrreducibleCharacter ↥(fixedSubgroup σ), (c β - d β) ^ 2 : ℤ) : ℂ) =
        ((1 : ℤ) : ℂ) := by
      rw [hcast, Int.cast_one]
      exact hparsC
    exact_mod_cast h
  -- ### Step 8: exactly one `β` with `c β ≠ d β`
  set S : Finset (IrreducibleCharacter ↥(fixedSubgroup σ)) :=
    Finset.univ.filter (fun β => c β - d β ≠ 0) with hSdef
  have hSsum : ∑ β ∈ S, (c β - d β) ^ 2 = 1 := by
    rw [← hparsZ, hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    by_cases h : c β - d β = 0
    · rw [ite_eq_right (by simpa using h), h]
      ring
    · rw [ite_eq_left h]
  have hge : ∀ β ∈ S, (1 : ℤ) ≤ (c β - d β) ^ 2 := by
    intro β hβ
    have hne : c β - d β ≠ 0 := by
      rw [hSdef, Finset.mem_filter] at hβ
      exact hβ.2
    have h1 : (1 : ℤ) ≤ |c β - d β| := Int.one_le_abs hne
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c β - d β| ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      _ = (c β - d β) ^ 2 := sq_abs _
  have hcardle : S.card ≤ 1 := by
    have h1 : ∑ β ∈ S, (1 : ℤ) ≤ ∑ β ∈ S, (c β - d β) ^ 2 := Finset.sum_le_sum hge
    rw [hSsum] at h1
    simpa using h1
  have hcardge : 1 ≤ S.card := by
    by_contra h
    have h0 : S.card = 0 := by omega
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty] at hSsum
    exact one_ne_zero hSsum.symm
  have hcard1 : S.card = 1 := le_antisymm hcardle hcardge
  have huniq : ∃! β : IrreducibleCharacter ↥(fixedSubgroup σ), c β - d β ≠ 0 := by
    obtain ⟨β₀, hβ₀⟩ := Finset.card_eq_one.mp hcard1
    have hmem₀ : β₀ ∈ S := by rw [hβ₀]; exact Finset.mem_singleton_self β₀
    have hβ₀ne : c β₀ - d β₀ ≠ 0 := by
      rw [hSdef, Finset.mem_filter] at hmem₀
      exact hmem₀.2
    refine ⟨β₀, hβ₀ne, ?_⟩
    intro β hβ
    have hmem : β ∈ S := by
      rw [hSdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hβ⟩
    rw [hβ₀] at hmem
    exact Finset.mem_singleton.mp hmem
  obtain ⟨β₀, hβ₀ne, hβ₀uniq⟩ := huniq
  have hsqβ₀ : (c β₀ - d β₀) ^ 2 = 1 := by
    have hsingle : S = {β₀} := by
      obtain ⟨γ, hγ⟩ := Finset.card_eq_one.mp hcard1
      rw [hγ, Finset.singleton_inj]
      exact hβ₀uniq γ (by
        have hmem : γ ∈ S := by rw [hγ]; exact Finset.mem_singleton_self γ
        rw [hSdef, Finset.mem_filter] at hmem
        exact hmem.2)
    rw [hsingle] at hSsum
    simpa using hSsum
  -- ### Step 9: multiplicities of `α|_{C_U(σ)}`
  have hmul : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      ClassFunction.inner (ClassFunction.restrict (fixedSubgroup σ) (α : ClassFunction U ℂ))
        (β : ClassFunction ↥(fixedSubgroup σ) ℂ) = ((c β + d β : ℤ) : ℂ) := by
    intro β
    have hres : ClassFunction.restrict (fixedSubgroup σ) (α : ClassFunction U ℂ) = νp + νm := by
      ext b
      rw [ClassFunction.restrict_apply, ClassFunction.add_apply, ← hνsum b, ← congrFun hρη,
        ← hηres (b : U)]
    rw [hres, ClassFunction.inner_add_left, hc' β, hd' β]
    push_cast
    ring
  -- ### Step 10: conclusion
  refine ⟨β₀, ?_, ?_⟩
  · show ∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict (fixedSubgroup σ)
        (α : ClassFunction U ℂ)) (β₀ : ClassFunction ↥(fixedSubgroup σ) ℂ) = (2 * k + 1 : ℂ)
    rw [hmul β₀]
    obtain ⟨k, hk⟩ := gw2_int_add_eq_two_mul_add_one_of_sq hsqβ₀
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  · intro β hβ
    obtain ⟨k, hk⟩ := hβ
    rw [hmul β] at hk
    have hk' : c β + d β = 2 * k + 1 := by
      have h2 : ((c β + d β : ℤ) : ℂ) = ((2 * k + 1 : ℤ) : ℂ) := by
        rw [hk]
        push_cast
        ring
      exact_mod_cast h2
    exact hβ₀uniq β (gw2_int_sub_ne_zero_of_add_eq_two_mul_add_one hk')

end Work.BG
