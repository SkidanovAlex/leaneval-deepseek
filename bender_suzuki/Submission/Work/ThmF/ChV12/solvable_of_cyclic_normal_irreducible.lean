import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.Fitting.commutator_le_fitting_of_isCyclic
import Submission.Work.ThmF.ChV12.mulAut_mul_comm_of_commute_of_irreducible
import Submission.Work.ThmF.ChV12.zpow_mem_of_invariant

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.ThmF.ChV12

/-- **Bender–Suzuki, Chapter V/VI: solvability from a cyclic normal irreducible subgroup.**

Let `A` be an elementary abelian `2`-group (`x * x = 1`, commutative) on which `D` acts
faithfully (`ρ`), and let `N ⊴ D` be cyclic with `A` irreducible under `N` (the only
`N`-invariant subgroups of `A` are `⊥` and `⊤`).  Then `D` is solvable.

`D / C_D(N)` embeds in `Aut(N)`, which is abelian because `N` is cyclic, so `D' ≤ C_D(N)`.
It remains to see that `C_D(N)` is abelian: it embeds into the centralizer of `σ = ρ t`
(`t` a generator of `N`) in `MulAut A`, which is commutative by
`mulAut_mul_comm_of_commute_of_irreducible`.  Hence `D` is metabelian. -/
theorem solvable_of_cyclic_normal_irreducible {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (N : Subgroup D) (hN : N.Normal) (hNcyc : IsCyclic ↥N)
    (hirr : ∀ W : Subgroup A, W ≠ ⊥ → (∀ t ∈ N, ∀ x ∈ W, ρ t x ∈ W) → W = ⊤) :
    Group.IsSolvable D := by
  classical
  letI : CommGroup A := { ‹Group A› with mul_comm := hAc }
  haveI : IsCyclic ↥N := hNcyc
  -- The centralizer of `N` in `D`.
  let C : Subgroup D := Subgroup.centralizer (N : Set D)
  haveI : C.Normal := Subgroup.normal_centralizer
  -- A generator `t` of `N` and the corresponding automorphism `σ = ρ t₀`.
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥N)
  let t₀ : D := (t : D)
  have hN_eq : Subgroup.zpowers t₀ = N := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]; exact t.2
    · intro n hn
      have h1 : (⟨n, hn⟩ : ↥N) ∈ Subgroup.zpowers t := ht ⟨n, hn⟩
      rw [Subgroup.mem_zpowers_iff] at h1
      obtain ⟨k, hk⟩ := h1
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, congrArg Subtype.val hk⟩
  -- `A` is irreducible with respect to the single automorphism `σ = ρ t₀`.
  have hσirr : ∀ W : Subgroup A, W ≠ ⊥ → (∀ x ∈ W, (ρ t₀) x ∈ W) → W = ⊤ := by
    intro W hWne hinv
    refine hirr W hWne (fun t' ht' x hx => ?_)
    have h1 : t' ∈ Subgroup.zpowers t₀ := by rw [hN_eq]; exact ht'
    rw [Subgroup.mem_zpowers_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have h2 : ρ t' = (ρ t₀) ^ k := by rw [← hk, map_zpow]
    rw [h2]
    exact zpow_mem_of_invariant (ρ t₀) W hinv k x hx
  -- `C` is commutative (the crux): it embeds in the centralizer of `σ` in `MulAut A`.
  have hCcomm : IsMulCommutative ↥C := by
    refine ⟨⟨fun d₁ d₂ => ?_⟩⟩
    apply Subtype.ext
    have hd₁ : (d₁ : D) ∈ Subgroup.centralizer (N : Set D) := d₁.2
    have hd₂ : (d₂ : D) ∈ Subgroup.centralizer (N : Set D) := d₂.2
    have hcomm₁ : (ρ t₀) * (ρ (d₁ : D)) = (ρ (d₁ : D)) * (ρ t₀) :=
      calc (ρ t₀) * (ρ (d₁ : D)) = ρ (t₀ * (d₁ : D)) := (map_mul ρ t₀ (d₁ : D)).symm
        _ = ρ ((d₁ : D) * t₀) := by rw [(Subgroup.mem_centralizer_iff.mp hd₁) t₀ t.2]
        _ = (ρ (d₁ : D)) * (ρ t₀) := map_mul ρ (d₁ : D) t₀
    have hcomm₂ : (ρ t₀) * (ρ (d₂ : D)) = (ρ (d₂ : D)) * (ρ t₀) :=
      calc (ρ t₀) * (ρ (d₂ : D)) = ρ (t₀ * (d₂ : D)) := (map_mul ρ t₀ (d₂ : D)).symm
        _ = ρ ((d₂ : D) * t₀) := by rw [(Subgroup.mem_centralizer_iff.mp hd₂) t₀ t.2]
        _ = (ρ (d₂ : D)) * (ρ t₀) := map_mul ρ (d₂ : D) t₀
    have hu : ∀ x : A, (ρ (d₁ : D)) ((ρ t₀) x) = (ρ t₀) ((ρ (d₁ : D)) x) :=
      fun x => (congrArg (fun f : MulAut A => f x) hcomm₁).symm
    have hv : ∀ x : A, (ρ (d₂ : D)) ((ρ t₀) x) = (ρ t₀) ((ρ (d₂ : D)) x) :=
      fun x => (congrArg (fun f : MulAut A => f x) hcomm₂).symm
    have hcrux : (ρ (d₁ : D)) * (ρ (d₂ : D)) = (ρ (d₂ : D)) * (ρ (d₁ : D)) :=
      mulAut_mul_comm_of_commute_of_irreducible (A := A) (ρ t₀) hσirr
        (ρ (d₁ : D)) (ρ (d₂ : D)) hu hv
    apply hfaith
    show ρ ((d₁ : D) * (d₂ : D)) = ρ ((d₂ : D) * (d₁ : D))
    rw [map_mul, map_mul]
    exact hcrux
  haveI : IsMulCommutative ↥C := hCcomm
  -- The kernel of the conjugation action on `N` is exactly `C`.
  have hker : (MulAut.conjNormal (H := N)).ker = C := by
    show (MulAut.conjNormal (H := N)).ker = Subgroup.centralizer (N : Set D)
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h n hn
      have h2 : g * n * g⁻¹ = n := by
        have h1 := congrArg Subtype.val (congrArg (fun f : MulAut ↥N => f ⟨n, hn⟩) h)
        rw [MulAut.conjNormal_apply] at h1
        simpa using h1
      calc n * g = (g * n * g⁻¹) * g := by rw [h2]
        _ = g * n := by group
    · intro h
      ext x
      obtain ⟨n, hn⟩ := x
      have h1 : n * g = g * n := h n hn
      rw [MulAut.conjNormal_apply]
      show g * n * g⁻¹ = n
      rw [← h1]; group
  -- The derived subgroup of `D` lies in `C`.
  have hcomm_le : commutator D ≤ C := by
    haveI : IsMulCommutative (MulAut ↥N) := Work.Fitting.isMulCommutative_mulAut_of_isCyclic
    change ⁅(⊤ : Subgroup D), ⊤⁆ ≤ C
    rw [← hker]
    refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  -- `D ⧸ C` is commutative, so `D` is a (metabelian) extension of `C` by it.
  haveI : IsMulCommutative (D ⧸ C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le
  exact Group.isSolvable_of_subgroup_quotient C

end Work.ThmF.ChV12
