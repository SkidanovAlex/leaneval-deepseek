import Mathlib
import Submission.Work.CORE4.A7FGB.involution_support_mem

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.CORE4.A7FGB

/-- A finite group with exactly four elements has exactly three non-identity elements. -/
lemma card_filter_ne_one_of_card_four {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (hH : Fintype.card H = 4) :
    (Finset.univ.filter (fun x : H => x ≠ 1)).card = 3 := by
  have h1 : (1 : H) ∈ (Finset.univ : Finset H) := Finset.mem_univ 1
  have hf : (Finset.univ.filter (fun x : H => x ≠ 1)) = Finset.univ.erase 1 := by
    ext x; simp
  rw [hf, Finset.card_erase_of_mem h1, Finset.card_univ, hH]

/-- The support of a conjugate is the image of the support under the conjugating element. -/
lemma support_conj (g v : alternatingGroup (Fin 7)) :
    ((g * v * g⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support
      = (g : Equiv.Perm (Fin 7)) • (v : Equiv.Perm (Fin 7)).support := by
  have h := Equiv.Perm.support_toConjAct_eq_smul_support
    (g : Equiv.Perm (Fin 7)) (v : Equiv.Perm (Fin 7))
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h
  have hcoe : (((g * v * g⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)))
      = (g : Equiv.Perm (Fin 7)) * (v : Equiv.Perm (Fin 7)) * (g : Equiv.Perm (Fin 7))⁻¹ := by
    simp
  rw [hcoe, h]

/-- In `A₇`, let `V` be a four-group whose non-identity elements are involutions with support the
fixed four-element set `T`, and let `R ≥ V`.  Then the number of involutions of `R` (elements of
order two) is at least three times the number of `R`-conjugates of `T`.

The stabilizer of `T` in `A₇` is exactly the normalizer of `V`: an element `g` fixing the set
`T` conjugates every non-identity element of `V` to an involution with support `T`, which by
`involution_support_mem` lies again in `V`; conversely a normalizer element conjugates a
non-identity element `v₀ ∈ V` to an element of `V` whose support equals both `T` and `g • T`.
Hence the index `[R : R ⊓ N(V)]` equals the length of the orbit of `T` under `R`.  That orbit is
a set of four-element subsets, and for every such subset `S` in it exactly three involutions of
`R` have support `S`: at most three because an involution with a fixed four-element support is
determined by its value at one point, and at least three because the three conjugates of the
non-identity elements of `V` by a suitable element of `R` qualify.  These fibres are disjoint,
which gives the count. -/
theorem involutions_ge_alt (R V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVR : V ≤ R) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T) :
    3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R ≤
      Nat.card {u : ↥R // orderOf u = 2} := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite V
  haveI : Fintype ↥R := Fintype.ofFinite R
  -- ## Step 1: the stabilizer of `T` in `A₇` is the normalizer of `V`.
  -- Every element fixing `T` conjugates `V` into `V`.
  have hconjmem : ∀ (a : alternatingGroup (Fin 7)), a • T = T → ∀ h ∈ V, a * h * a⁻¹ ∈ V := by
    intro a ha h hh
    rcases eq_or_ne h 1 with rfl | h1
    · simp
    · have haperm : (a : Equiv.Perm (Fin 7)) • T = T := by
        have h2' := ha
        rw [MulAction.subgroup_smul_def] at h2'
        exact h2'
      have hw2 : (a * h * a⁻¹) * (a * h * a⁻¹) = 1 := by
        rw [show (a * h * a⁻¹) * (a * h * a⁻¹) = a * (h * h) * a⁻¹ from by group]
        rw [h2 h hh]; group
      have hwne : a * h * a⁻¹ ≠ 1 := by
        intro hc
        apply h1
        calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
          _ = a⁻¹ * 1 * a := by rw [hc]
          _ = 1 := by group
      have hws : ((a * h * a⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = T := by
        rw [support_conj a h, hsupp h hh h1, haperm]
      exact involution_support_mem V T hT hVcard h2 hsupp (a * h * a⁻¹) hw2 hwne hws
  have hstab : MulAction.stabilizer (alternatingGroup (Fin 7)) T =
      Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) := by
    apply le_antisymm
    · intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg
      have hginv : g⁻¹ • T = T := by
        have h : g⁻¹ • (g • T) = g⁻¹ • T := by rw [hg]
        rw [← mul_smul, inv_mul_cancel, one_smul] at h
        exact h.symm
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; exact hconjmem g hg h hh
      · intro hh
        have hc := hconjmem g⁻¹ hginv (g * h * g⁻¹) hh
        rwa [show g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h from by group] at hc
    · intro g hg
      rw [MulAction.mem_stabilizer_iff]
      rw [Subgroup.mem_normalizer_iff] at hg
      obtain ⟨v0, hv0⟩ : ∃ v0 : ↥V, v0 ≠ 1 := by
        have hlt : 1 < Fintype.card ↥V := by
          rw [← Nat.card_eq_fintype_card]; omega
        exact Fintype.exists_ne_of_one_lt_card hlt 1
      have hv0G : (v0 : alternatingGroup (Fin 7)) ≠ 1 := fun hc => hv0 (Subtype.ext hc)
      have hconjmem' : g * (v0 : alternatingGroup (Fin 7)) * g⁻¹ ∈ V := (hg _).mp v0.2
      have hconjne : g * (v0 : alternatingGroup (Fin 7)) * g⁻¹ ≠ 1 := by
        intro hc
        apply hv0G
        calc (v0 : alternatingGroup (Fin 7))
            = g⁻¹ * (g * (v0 : alternatingGroup (Fin 7)) * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hc]
          _ = 1 := by group
      have h1 : ((g * (v0 : alternatingGroup (Fin 7)) * g⁻¹ : alternatingGroup (Fin 7)) :
          Equiv.Perm (Fin 7)).support = T := hsupp _ hconjmem' hconjne
      have h2' : ((g * (v0 : alternatingGroup (Fin 7)) * g⁻¹ : alternatingGroup (Fin 7)) :
          Equiv.Perm (Fin 7)).support = (g : Equiv.Perm (Fin 7)) • T := by
        rw [support_conj g (v0 : alternatingGroup (Fin 7)), hsupp _ v0.2 hv0G]
      have hperm : (g : Equiv.Perm (Fin 7)) • T = T := by rw [← h2', h1]
      rw [MulAction.subgroup_smul_def]; exact hperm
  -- ## Step 2: counting.
  let Y : Finset (Finset (Fin 7)) := (MulAction.orbit ↥R T).toFinite.toFinset
  have hYcard : Y.card = (MulAction.orbit ↥R T).ncard := (Set.ncard_eq_toFinset_card _ _).symm
  let fib : Finset (Fin 7) → Finset ↥R := fun S =>
    Finset.univ.filter (fun u : ↥R => orderOf u = 2 ∧ (u : Equiv.Perm (Fin 7)).support = S)
  let Z : Finset ↥R := Y.biUnion fib
  -- At most three involutions of `A₇` have a given four-element support.
  have hfib_le_three : ∀ S : Finset (Fin 7), S.card = 4 → (fib S).card ≤ 3 := by
    intro S hS
    have hinjAR : Function.Injective (fun u : ↥R => (u : alternatingGroup (Fin 7))) :=
      fun _ _ hab => Subtype.ext hab
    have hsubset : (fib S).image (fun u : ↥R => (u : alternatingGroup (Fin 7))) ⊆
        Finset.univ.filter (fun x : alternatingGroup (Fin 7) =>
          x * x = 1 ∧ x ≠ 1 ∧ (x : Equiv.Perm (Fin 7)).support = S) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      rw [Finset.mem_filter] at hu ⊢
      obtain ⟨-, huord, husupp⟩ := hu
      refine ⟨Finset.mem_univ _, ?_, ?_, husupp⟩
      · have hu2 : u ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [huord])
        have huu : (u : ↥R) * u = 1 := by rwa [pow_two] at hu2
        have hcc := congrArg (fun t : ↥R => (t : alternatingGroup (Fin 7))) huu
        simpa using hcc
      · intro hc
        have h1 : (u : Equiv.Perm (Fin 7)) = 1 :=
          congrArg (fun t : alternatingGroup (Fin 7) => (t : Equiv.Perm (Fin 7))) hc
        rw [h1] at husupp
        have : S.card = 0 := by rw [← husupp]; simp
        omega
    calc (fib S).card
        = ((fib S).image (fun u : ↥R => (u : alternatingGroup (Fin 7)))).card :=
          (Finset.card_image_of_injective _ hinjAR).symm
      _ ≤ (Finset.univ.filter (fun x : alternatingGroup (Fin 7) =>
            x * x = 1 ∧ x ≠ 1 ∧ (x : Equiv.Perm (Fin 7)).support = S)).card :=
          Finset.card_le_card hsubset
      _ ≤ 3 := card_involutions_support_le_three S hS
  have hfib3 : ∀ S ∈ Y, (fib S).card = 3 := by
    intro S hS
    have hSorb : S ∈ MulAction.orbit ↥R T := (Set.Finite.mem_toFinset _).mp hS
    obtain ⟨r, hr⟩ := MulAction.mem_orbit_iff.mp hSorb
    have hScard : S.card = 4 := by
      have h : (r • T).card = T.card := by
        rw [Finset.smul_finset_def]
        have hh : (fun x : Fin 7 => r • x) = (fun x => (r : Equiv.Perm (Fin 7)) x) := by
          funext x; rw [MulAction.subgroup_smul_def]; rfl
        rw [hh, Finset.card_image_of_injective _ (r : Equiv.Perm (Fin 7)).injective]
      rw [← hr, h, hT]
    have hfible : (fib S).card ≤ 3 := hfib_le_three S hScard
    -- lower bound: the three conjugates of the non-identity elements of `V`
    let gv : ↥V → ↥R := fun v =>
      ⟨(r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
          * (r : alternatingGroup (Fin 7))⁻¹,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ r.2 (hVR v.2)) (Subgroup.inv_mem _ r.2)⟩
    have hgv_inj : Function.Injective gv := by
      intro a b hab
      have hab' : (r : alternatingGroup (Fin 7)) * (a : alternatingGroup (Fin 7))
            * (r : alternatingGroup (Fin 7))⁻¹
          = (r : alternatingGroup (Fin 7)) * (b : alternatingGroup (Fin 7))
            * (r : alternatingGroup (Fin 7))⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel hab'))
    have hV3 : (Finset.univ.filter (fun v : ↥V => v ≠ 1)).card = 3 :=
      card_filter_ne_one_of_card_four (by rw [← Nat.card_eq_fintype_card]; exact hVcard)
    have hgv_card : ((Finset.univ.filter (fun v : ↥V => v ≠ 1)).image gv).card = 3 := by
      rw [Finset.card_image_of_injective _ hgv_inj, hV3]
    have hgv_sub : (Finset.univ.filter (fun v : ↥V => v ≠ 1)).image gv ⊆ fib S := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [Finset.mem_filter] at hv ⊢
      obtain ⟨-, hvne⟩ := hv
      have hvneG : (v : alternatingGroup (Fin 7)) ≠ 1 := fun hc => hvne (Subtype.ext hc)
      have hsupp_v : (v : Equiv.Perm (Fin 7)).support = T := hsupp _ v.2 hvneG
      have hconj : ((gv v : ↥R) : Equiv.Perm (Fin 7))
          = (((r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
              * (r : alternatingGroup (Fin 7))⁻¹ : alternatingGroup (Fin 7)) :
              Equiv.Perm (Fin 7)) := by
        dsimp [gv]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · -- the conjugate has order two
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two]
          apply Subtype.ext
          show ((r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
              * (r : alternatingGroup (Fin 7))⁻¹)
              * ((r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
              * (r : alternatingGroup (Fin 7))⁻¹) = 1
          calc ((r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
                  * (r : alternatingGroup (Fin 7))⁻¹)
                  * ((r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
                  * (r : alternatingGroup (Fin 7))⁻¹)
                = (r : alternatingGroup (Fin 7)) * ((v : alternatingGroup (Fin 7))
                    * (v : alternatingGroup (Fin 7))) * (r : alternatingGroup (Fin 7))⁻¹ :=
                  by group
            _ = (r : alternatingGroup (Fin 7)) * 1 * (r : alternatingGroup (Fin 7))⁻¹ := by
                  rw [h2 v v.2]
            _ = 1 := by group
        · intro hc
          have h1 : (r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
              * (r : alternatingGroup (Fin 7))⁻¹ = 1 := by
            have hcc := congrArg (fun t : ↥R => (t : alternatingGroup (Fin 7))) hc
            simpa [gv] using hcc
          apply hvneG
          calc (v : alternatingGroup (Fin 7))
              = (r : alternatingGroup (Fin 7))⁻¹
                  * ((r : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7))
                    * (r : alternatingGroup (Fin 7))⁻¹) * (r : alternatingGroup (Fin 7)) := by
                group
            _ = 1 := by rw [h1]; group
      · -- the conjugate is supported on `S`
        rw [hconj, support_conj (r : alternatingGroup (Fin 7)) (v : alternatingGroup (Fin 7)),
          hsupp_v]
        have hsmul : (r : Equiv.Perm (Fin 7)) • T = r • T := by
          simp only [MulAction.subgroup_smul_def]
        rw [hsmul, hr]
    have hfibge : 3 ≤ (fib S).card := by
      rw [← hgv_card]
      exact Finset.card_le_card hgv_sub
    omega
  have hdisj : (↑Y : Set (Finset (Fin 7))).PairwiseDisjoint fib := by
    rw [Finset.pairwiseDisjoint_iff]
    intro S _ S' _ hne
    obtain ⟨u, hu⟩ := hne
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    obtain ⟨-, -, h1⟩ := Finset.mem_filter.mp hu1
    obtain ⟨-, -, h2⟩ := Finset.mem_filter.mp hu2
    rw [← h1, h2]
  have hZcard : Z.card = 3 * Y.card := by
    rw [Finset.card_biUnion hdisj,
      Finset.sum_congr rfl (fun S hS => hfib3 S hS),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hZsub : Z ⊆ Finset.univ.filter (fun u : ↥R => orderOf u = 2) := by
    intro u hu
    rw [Finset.mem_biUnion] at hu
    obtain ⟨S, -, huS⟩ := hu
    rw [Finset.mem_filter] at huS ⊢
    exact ⟨Finset.mem_univ _, huS.2.1⟩
  have hmain : 3 * Y.card ≤ Nat.card {u : ↥R // orderOf u = 2} := by
    rw [← hZcard]
    calc Z.card ≤ (Finset.univ.filter (fun u : ↥R => orderOf u = 2)).card :=
          Finset.card_le_card hZsub
      _ = Nat.card {u : ↥R // orderOf u = 2} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hrel : (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R =
      Y.card := by
    rw [Subgroup.inf_relIndex_left, Subgroup.relIndex, ← hstab, MulAction.stabilizer_subgroupOf,
      MulAction.index_stabilizer]
    exact hYcard.symm
  calc 3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R
      = 3 * Y.card := by rw [hrel]
    _ ≤ Nat.card {u : ↥R // orderOf u = 2} := hmain

end Work.CORE4.A7FGB
