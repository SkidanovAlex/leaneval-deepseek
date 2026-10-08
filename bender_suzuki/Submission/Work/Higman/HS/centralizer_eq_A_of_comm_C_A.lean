import Mathlib
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.RedAux.deriv_eq_sq_false
import Submission.Work.Higman.RedAux.abelian_case
import Submission.Work.Higman.higman_lemma2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.HS

open scoped commutatorElement

/-- A subgroup invariant under an automorphism has invariant centralizer. -/
theorem centralizer_map_xi_eq_aux {P : Type} [Group P] {A : Subgroup P} (ξ : MulAut P)
    (hAinv : A.map (ξ : MulAut P).toMonoidHom = A) :
    (Subgroup.centralizer (A : Set P)).map (ξ : MulAut P).toMonoidHom
      = Subgroup.centralizer (A : Set P) := by
  have mem_iff : ∀ g : P, (∀ a ∈ A, a * g = g * a) ↔
      g ∈ Subgroup.centralizer (A : Set P) := fun g => Subgroup.mem_centralizer_iff
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    refine (mem_iff (ξ x)).mpr ?_
    intro a ha
    have hx' := (mem_iff x).mp hx
    have h1 := hx' ((ξ : MulAut P).symm a) (Work.Higman.symm_mem_of_map_eq ξ hAinv ha)
    calc a * ξ x = ξ ((ξ : MulAut P).symm a) * ξ x := by simp
      _ = ξ ((ξ : MulAut P).symm a * x) := by simp
      _ = ξ (x * (ξ : MulAut P).symm a) := by rw [h1]
      _ = ξ x * a := by simp
  · intro y hy
    refine ⟨(ξ : MulAut P).symm y, ?_, by simp⟩
    refine (mem_iff ((ξ : MulAut P).symm y)).mpr ?_
    intro a ha
    have hy' := (mem_iff y).mp hy
    have h2 : ξ a ∈ A := by
      have h3 := Subgroup.mem_map_of_mem (ξ : MulAut P).toMonoidHom ha
      rwa [hAinv] at h3
    have h1 := hy' (ξ a) h2
    have h4 : a * (ξ : MulAut P).symm y = (ξ : MulAut P).symm y * a := by
      have := congrArg (ξ : MulAut P).symm h1
      simpa using this
    exact h4

/-- **`C_P(A) = A` in the `C₄`-covering configuration.**

Let `P` be a Suzuki 2-group and `A ⊴ P` abelian, `ξ`-invariant, with `Ω₁(P) ≤ A`,
`⁅P,P⁆ = A`, every square of `P` in `A`, `A⁴ = ⊥`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`.
Then the centraliser of `A` is `A`.

The proof uses only the structure of `A` and a minimal `ξ`-invariant normal subgroup
`A < F ≤ C_P(A)`: the key observation is that an element `x` of `C_P(A)` with `x² ∈ A²`
lies in `A` (if `x² = a²` with `a ∈ A`, then `(x a)² = x⁴ = 1` because `x` commutes with `a`
and `A⁴ = ⊥`, so `x a ∈ Ω₁(P) ≤ A`), which rules out `F² = A²` at once.  The remaining
possibilities `F² = A` are dispatched by the three clean lemmas `RedAux.abelian_case`,
`RedAux.deriv_eq_sq_false` and `MSA.lemma8_clean`. -/
theorem centralizer_eq_A_of_comm_C_A {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) :
    Subgroup.centralizer (A : Set P) = A := by
  classical
  set K : Subgroup P := Subgroup.centralizer (A : Set P) with hK
  have hAK : A ≤ K := by
    intro a ha
    rw [hK, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hAab y hy a ha
  -- **Key lemma**: an element of `C_P(A)` whose square lies in `A²` already lies in `A`.
  have hkey : ∀ x ∈ K, x ^ 2 ∈ Work.Higman.powSub A 2 → x ∈ A := by
    intro x hxK hx2
    have hxK' : x ∈ Subgroup.centralizer (A : Set P) := by rwa [hK] at hxK
    obtain ⟨a, ha, haeq⟩ := (Work.Higman.mem_powSub_iff hAab).mp hx2
    have hcomm : x * a = a * x := (Subgroup.mem_centralizer_iff.mp hxK' a ha).symm
    have ha4 : a ^ 4 = 1 := by
      have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub ha
      rw [hA4] at hmem
      simpa using hmem
    have hx4 : (x ^ 2) ^ 2 = 1 := by rw [← haeq, ← pow_mul]; exact ha4
    have hsq : (x * a) ^ 2 = 1 := by
      rw [Commute.mul_pow hcomm, haeq, ← pow_two]; exact hx4
    have hmem : x * a ∈ A := hNA (h.mem_omega1.mpr hsq)
    have : x = (x * a) * a⁻¹ := by group
    rw [this]
    exact A.mul_mem hmem (A.inv_mem ha)
  -- `A ≠ A²`, from `|A| = |Ω₁(P)|²` and `4 ≤ |Ω₁(P)|`.
  have hAne2 : A ≠ Work.Higman.powSub A 2 := by
    intro heq
    have hc : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun X : Subgroup P => Nat.card ↥X) heq
    rw [htop] at hc
    have hq : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
      rw [← hcard, hc]
    have h4 := h.omega1_card_ge_four
    have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
    nlinarith [hq, h4, hpos]
  refine le_antisymm ?_ hAK
  by_contra hKA
  -- `K > A`: choose `F` minimal with `A < F ≤ K`.
  have hKAne : K ≠ A := fun hEq => hKA (le_of_eq hEq)
  have hKn : K.Normal := by rw [hK]; infer_instance
  have hKinv : K.map (h.xi : MulAut P).toMonoidHom = K := by
    rw [hK]; exact centralizer_map_xi_eq_aux h.xi hAxi
  obtain ⟨F, hFn, hFinv, hAF, hFK, hFA, hcoverF⟩ :=
    Work.Higman.MSA.exists_minimal_covering h (A := A) (M := K) hKn hKinv hAK hKAne
  -- any subgroup containing `A` is normal, because `⁅P,P⁆ = A`
  have hnorm_of_le : ∀ D : Subgroup P, A ≤ D → D.Normal := by
    intro D hAD
    refine Subgroup.Normal.mk fun n hn g => ?_
    have h1 : ⁅g, n⁆ ∈ A := by
      rw [← hGs]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [show g * n * g⁻¹ = ⁅g, n⁆ * n from by rw [commutatorElement_def]; group]
    exact D.mul_mem (hAD h1) hn
  -- the version of `hcoverF` used by the clean case lemmas (no `Normal` hypothesis)
  have hcoverF' : ∀ D : Subgroup P, A ≤ D → D ≤ F →
      D.map (h.xi : MulAut P).toMonoidHom = D → D = A ∨ D = F :=
    fun D hAD hDF hDinv => hcoverF D (hnorm_of_le D hAD) hDinv hAD hDF
  -- squares of `F` lie in `A`
  have hF2leA : Work.Higman.powSub F 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hF2inv : (Work.Higman.powSub F 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub F 2 := Work.Higman.map_powSub (h.xi : MulAut P) hFinv 2
  have hFFleA : (⁅F, F⁆ : Subgroup P) ≤ A := by
    calc ⁅F, F⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = A := hGs
  have hFFinv : (⁅F, F⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅F, F⁆ := by
    rw [Subgroup.map_commutator, hFinv]
  rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hF2leA hF2inv with hF2bot | hF2A2 | hF2A
  · -- `F² = ⊥`: then `F ≤ Ω₁(P) ≤ A`
    have hFleOm : F ≤ Work.Higman.omega1 P := by
      intro x hx
      rw [h.mem_omega1]
      have : x ^ 2 ∈ Work.Higman.powSub F 2 := Work.Higman.pow_mem_powSub hx
      rw [hF2bot] at this
      simpa using this
    exact hFA (le_antisymm (hFleOm.trans hNA) hAF)
  · -- `F² = A²`: the key lemma forces `F ≤ A`
    have hFleA : F ≤ A := by
      intro x hx
      refine hkey x (hFK hx) ?_
      have : x ^ 2 ∈ Work.Higman.powSub F 2 := Work.Higman.pow_mem_powSub hx
      rwa [hF2A2] at this
    exact hFA (le_antisymm hFleA hAF)
  · -- `F² = A`: split on `[F,F]`
    rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hFFleA hFFinv with hFFbot | hFFA2 | hFFA
    · -- `[F,F] = ⊥`: `F` is abelian, excluded by Higman's Lemma 8 machinery
      have hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
        intro x hx y hy
        have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hFFbot]
          exact Subgroup.commutator_mem_commutator hx hy
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      exact Work.Higman.RedAux.abelian_case h hAxi hAab hNA hGs hsq hA4 htop hcard
        hAF hFA hFinv hFab hF2A hcoverF'
    · -- `[F,F] = A²`: impossible by Higman's Lemma 8 (the `E' = A²`, `E² = A` case)
      exact Work.Higman.RedAux.deriv_eq_sq_false h hAxi hAab hNA hGs hsq hA4 htop hcard
        hAF hFA hFinv hcoverF' hFFA2 hF2A
    · -- `[F,F] = A`: Higman's Lemma 8 gives `A ≤ Ω₁(P) = A²`, contradicting `A ≠ A²`
      have hAA : ∀ a ∈ A, a * a = 1 :=
        Work.Higman.MSA.lemma8_clean h ⟨hAn, hAxi, hAab⟩ hFn hFinv hAF hFA.symm hcoverF
          hF2leA hFFA
      have hAle : A ≤ Work.Higman.powSub A 2 := by
        intro a ha
        rw [htop]
        exact h.mem_omega1.mpr (by rw [pow_two]; exact hAA a ha)
      exact hAne2 (le_antisymm hAle (Work.Higman.powSub_le (by norm_num)))

end Work.Higman.HS
