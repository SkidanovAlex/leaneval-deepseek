import Mathlib
import Submission.Work.CharPrelim.FrobModAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Modular Frobenius fixed-point dimension formula, algebraically closed coefficient field
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

open Classical
open scoped MonoidAlgebra Pointwise

namespace Work.CharPrelim

/-- The invariants of a restricted representation, as a subspace. -/
lemma invariants_restrict_map {k : Type*} [Field k] {L : Type*} [Group L]
    {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k L W) (M : Submodule k W)
    (hM : ∀ g : L, ∀ u ∈ M, ρ g u ∈ M) (H : Subgroup L) :
    (Representation.invariants ((repRestrict ρ M hM).comp H.subtype)).map (Submodule.subtype M)
      = Representation.invariants (ρ.comp H.subtype) ⊓ M := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, v.2⟩
    refine (Representation.mem_invariants _ _).mpr ?_
    intro h
    have hh := (Representation.mem_invariants _ _).mp hv h
    simpa [repRestrict_apply] using congrArg (fun u : M => (u : W)) hh
  · intro hw
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
    refine ⟨⟨w, hw2⟩, (Representation.mem_invariants _ _).mpr ?_, rfl⟩
    intro h
    apply Subtype.ext
    have hh := (Representation.mem_invariants _ _).mp hw1 h
    simpa [repRestrict_apply] using hh

/-- The finrank form of the previous lemma. -/
lemma finrank_invariants_restrict {k : Type*} [Field k] {L : Type*} [Group L]
    {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k L W) (M : Submodule k W)
    (hM : ∀ g : L, ∀ u ∈ M, ρ g u ∈ M) (H : Subgroup L) :
    Module.finrank k ↥(Representation.invariants ((repRestrict ρ M hM).comp H.subtype))
      = Module.finrank k ↥(Representation.invariants (ρ.comp H.subtype) ⊓ M) := by
  have h := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Submodule.subtype M)
    Subtype.coe_injective (Representation.invariants ((repRestrict ρ M hM).comp H.subtype)))
  rw [invariants_restrict_map ρ M hM H] at h
  exact h

/-- Auxiliary strong induction form of the modular Frobenius fixed point formula. -/
theorem frobenius_finrank_aux {k : Type*} [Field k] [IsAlgClosed k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {L : Type*} [Group L] [Fintype L] {K E : Subgroup L} (hKn : K.Normal)
    (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set L) ≤ K) (hpL : ¬ p ∣ Nat.card L)
    (E₀ : Subgroup L) (hE₀ : E₀ ≤ E) (n : ℕ) :
     ∀ (W' : Type*) [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'],
      Module.finrank k W' = n → ∀ (ρ' : Representation k L W'),
      Representation.invariants (ρ'.comp K.subtype) = ⊥ →
      Nat.card ↥E₀ * Module.finrank k ↥(Representation.invariants (ρ'.comp E₀.subtype))
        = Module.finrank k W' := by
  classical
  haveI : K.Normal := hKn
  haveI : Fintype ↥K := Fintype.ofFinite _
  haveI : Fintype ↥E := Fintype.ofFinite _
  haveI : Fintype ↥E₀ := Fintype.ofFinite _
  haveI : Fintype ↥(E₀.subgroupOf E) := Fintype.ofFinite _
  have hpK : ¬ p ∣ Nat.card ↥K := fun h => hpL (h.trans (Subgroup.card_subgroup_dvd_card K))
  have hcardK : (Fintype.card ↥K : k) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h0 => hpK ((CharP.cast_eq_zero_iff k p (Nat.card ↥K)).mp h0)
  have hcardL : (Fintype.card ↥(⊤ : Subgroup L) : k) ≠ 0 := by
    have h1 : Fintype.card ↥(⊤ : Subgroup L) = Nat.card L := by
      rw [← Nat.card_eq_fintype_card, Subgroup.card_top]
    rw [h1]
    exact fun h0 => hpL ((CharP.cast_eq_zero_iff k p (Nat.card L)).mp h0)
  have hidx : Nat.card ↥E₀ * (E₀.subgroupOf E).index = Nat.card ↥E := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀).toEquiv]
    exact Subgroup.card_mul_index (E₀.subgroupOf E)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro W' _ _ _ hdim ρ' hfix'
      by_cases htriv : Subsingleton W'
      · have h1 : Module.finrank k W' = 0 := Module.finrank_zero_of_subsingleton
        have h2 : Module.finrank k ↥(Representation.invariants (ρ'.comp E₀.subtype)) = 0 :=
          Module.finrank_zero_of_subsingleton
        rw [h1, h2, Nat.mul_zero]
      · haveI : Nontrivial W' := not_subsingleton_iff_nontrivial.mp htriv
        obtain ⟨U, hUstab, hUne, hUmin⟩ := exists_isSimpleStable ρ' K
        have hsU : IsSimpleStable ρ' K U := ⟨hUstab, hUne, hUmin⟩
        have hUK : ∀ u ∈ U, (∀ x : ↥K, ρ' (x : L) u = u) → u = 0 := by
          intro u hu hfu
          have hmem : u ∈ Representation.invariants (ρ'.comp K.subtype) :=
            (Representation.mem_invariants _ _).mpr (fun x => hfu x)
          rw [hfix'] at hmem
          simpa using hmem
        obtain ⟨π, hπfix, hπeq⟩ := exists_equivariant_retraction ρ' K hUstab hcardK
        have hdirect : ∀ (v : ↥E → W'), (∀ e : ↥E, v e ∈ U.map (ρ' (e : L))) →
            ∑ e : ↥E, v e = 0 → ∀ e : ↥E, v e = 0 :=
          fun v hv hsum => sum_eq_zero_of_conj (hU := hUstab) ρ' hinf hcent hpK hsU hUK
            hπfix hπeq v hv hsum
        set M : Submodule k W' := orbitModule ρ' E U with hMdef
        have hMstab : ∀ g : L, ∀ w ∈ M, ρ' g w ∈ M := orbitModule_stable ρ' hsup hUstab
        have hMle : U ≤ M := by
          intro u hu
          exact le_orbitModule ρ' E U 1 ⟨u, hu, by simp⟩
        have hMne : M ≠ ⊥ := by
          intro h
          exact hUne (le_bot_iff.mp (h ▸ hMle))
        have hMinv : Module.finrank k ↥(Representation.invariants
            ((repRestrict ρ' M hMstab).comp E₀.subtype))
            = (E₀.subgroupOf E).index * Module.finrank k ↥U := by
          have h1 := finrank_invariants_orbitModule ρ' E hsup hUstab hdirect (E₀.subgroupOf E)
          have heqinv : Representation.invariants
              ((repRestrict ρ' M hMstab).comp ((Subgroup.subtype E).comp (E₀.subgroupOf E).subtype))
              = Representation.invariants ((repRestrict ρ' M hMstab).comp E₀.subtype) := by
            ext v
            constructor
            · intro hv z
              exact hv ⟨⟨(z : L), hE₀ z.2⟩, z.2⟩
            · intro hv z
              exact hv ⟨((z : ↥E) : L), z.2⟩
          rw [heqinv] at h1
          exact h1
        have hMdim : Module.finrank k ↥M = Nat.card ↥E * Module.finrank k ↥U :=
          finrank_orbitModule ρ' E U hdirect
        have hMcard : Nat.card ↥E₀ * Module.finrank k ↥(Representation.invariants
            ((repRestrict ρ' M hMstab).comp E₀.subtype)) = Module.finrank k ↥M := by
          rw [hMinv, hMdim, ← mul_assoc, hidx]
        by_cases hMtop : M = ⊤
        · have h1 : Module.finrank k ↥(Representation.invariants (ρ'.comp E₀.subtype))
              = Module.finrank k ↥(Representation.invariants
                  ((repRestrict ρ' M hMstab).comp E₀.subtype)) := by
            rw [finrank_invariants_restrict ρ' M hMstab E₀, hMtop, inf_top_eq]
          have h2 : Module.finrank k ↥M = Module.finrank k W' := by
            rw [hMtop]
            exact LinearEquiv.finrank_eq Submodule.topEquiv
          rw [h1, ← h2]
          exact hMcard
        · have hMstabTop : IsStable ρ' ⊤ M := fun x w hw => hMstab (x : L) w hw
          obtain ⟨πM, hπMfix, hπMeq⟩ := exists_equivariant_retraction ρ' ⊤ hMstabTop hcardL
          set P : W' →ₗ[k] W' := M.subtype.comp πM with hPdef
          have hPmem : ∀ w : W', P w ∈ M := fun w => (πM w).2
          have hPfix : ∀ w ∈ M, P w = w := by
            intro w hw
            show M.subtype (πM w) = w
            rw [hπMfix ⟨w, hw⟩]
            rfl
          have hPequiv : ∀ (g : L) (w : W'), P (ρ' g w) = ρ' g (P w) := by
            intro g w
            have h := hπMeq ⟨g, Subgroup.mem_top g⟩ w
            show M.subtype (πM (ρ' g w)) = ρ' g (M.subtype (πM w))
            rw [h]
            rfl
          set N : Submodule k W' := LinearMap.ker P with hNdef
          have hNstab : ∀ g : L, ∀ w ∈ N, ρ' g w ∈ N := by
            intro g w hw
            rw [hNdef, LinearMap.mem_ker] at hw ⊢
            rw [hPequiv g w, hw, map_zero]
          have hMNbot : M ⊓ N = ⊥ := by
            rw [Submodule.eq_bot_iff]
            intro w hw
            obtain ⟨hwM, hwN⟩ := Submodule.mem_inf.mp hw
            rw [hNdef, LinearMap.mem_ker] at hwN
            rw [hPfix w hwM] at hwN
            exact hwN
          have hMNtop : M ⊔ N = ⊤ := by
            rw [Submodule.eq_top_iff']
            intro w
            have h1 : P w ∈ M := hPmem w
            have h2 : w - P w ∈ N := by
              rw [hNdef, LinearMap.mem_ker]
              rw [map_sub, hPfix (P w) (hPmem w), sub_self]
            have hw : w = P w + (w - P w) := by abel
            rw [hw]
            exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
          have hNfix : Representation.invariants ((repRestrict ρ' N hNstab).comp K.subtype) = ⊥ := by
            rw [Submodule.eq_bot_iff]
            intro w hw
            apply Subtype.ext
            have hmem : (w : W') ∈ Representation.invariants (ρ'.comp K.subtype) := by
              refine (Representation.mem_invariants _ _).mpr ?_
              intro x
              have h := (Representation.mem_invariants _ _).mp hw x
              simpa [repRestrict_apply] using congrArg (fun u : N => (u : W')) h
            rw [hfix'] at hmem
            simpa using hmem
          have hNlt : Module.finrank k ↥N < n := by
            rw [← hdim]
            refine Submodule.finrank_lt ?_
            intro htop
            have hPzero : P = 0 := by
              ext w
              have hw : w ∈ N := by rw [htop]; exact Submodule.mem_top
              rw [hNdef, LinearMap.mem_ker] at hw
              exact hw
            obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
            have h1 : P u = u := hPfix u hu
            rw [hPzero] at h1
            exact hu0 h1.symm
          have hNIH := ih (Module.finrank k ↥N) hNlt N rfl (repRestrict ρ' N hNstab) hNfix
          have hVin : Module.finrank k ↥(Representation.invariants (ρ'.comp E₀.subtype))
              = Module.finrank k ↥(Representation.invariants
                  ((repRestrict ρ' M hMstab).comp E₀.subtype))
                + Module.finrank k ↥(Representation.invariants
                  ((repRestrict ρ' N hNstab).comp E₀.subtype)) := by
            set V : Submodule k W' := Representation.invariants (ρ'.comp E₀.subtype) with hV
            set VM : Submodule k W' := (Representation.invariants
              ((repRestrict ρ' M hMstab).comp E₀.subtype)).map (Submodule.subtype M) with hVM
            set VN : Submodule k W' := (Representation.invariants
              ((repRestrict ρ' N hNstab).comp E₀.subtype)).map (Submodule.subtype N) with hVN
            have hVMle : VM ≤ M := Submodule.map_subtype_le _ _
            have hVNle : VN ≤ N := Submodule.map_subtype_le _ _
            have hVNmem : ∀ w ∈ VN, w - P w = w := by
              intro w hw
              have hwN : w ∈ N := hVNle hw
              have hwE : ∀ z : ↥E₀, ρ' (z : L) w = w := by
                obtain ⟨b, hb, rfl⟩ := hw
                exact fun z => congrArg (fun v : ↥N => (v : W'))
                  ((Representation.mem_invariants _ _).mp hb z)
              rw [hNdef, LinearMap.mem_ker] at hwN
              rw [hwN]
              exact (sub_eq_self).mpr rfl
            have hVeq : V = VM ⊔ VN := by
              apply le_antisymm
              · intro w hw
                have hwE : ∀ z : ↥E₀, ρ' (z : L) w = w :=
                  (Representation.mem_invariants _ _).mp hw
                have hmemM : (⟨P w, hPmem w⟩ : ↥M) ∈ Representation.invariants
                    ((repRestrict ρ' M hMstab).comp E₀.subtype) := by
                  refine (Representation.mem_invariants _ _).mpr ?_
                  intro z
                  apply Subtype.ext
                  change ρ' (z : L) (P w) = P w
                  rw [← hPequiv (z : L) w, hwE z]
                have hker : w - P w ∈ N := by
                  rw [hNdef, LinearMap.mem_ker]
                  rw [map_sub, hPfix (P w) (hPmem w), sub_self]
                have hmemN : (⟨w - P w, hker⟩ : ↥N) ∈ Representation.invariants
                    ((repRestrict ρ' N hNstab).comp E₀.subtype) := by
                  refine (Representation.mem_invariants _ _).mpr ?_
                  intro z
                  apply Subtype.ext
                  change ρ' (z : L) (w - P w) = w - P w
                  rw [map_sub, hwE z, ← hPequiv (z : L) w, hwE z]
                refine Submodule.mem_sup.mpr ⟨P w, ?_, w - P w, ?_, by abel⟩
                · exact ⟨⟨P w, hPmem w⟩, hmemM, rfl⟩
                · exact ⟨⟨w - P w, hker⟩, hmemN, rfl⟩
              · intro w hw
                obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
                obtain ⟨a', ha', rfl⟩ := ha
                obtain ⟨b', hb', rfl⟩ := hb
                have haE : ∀ z : ↥E₀, (ρ'.comp E₀.subtype) z (M.subtype a') = M.subtype a' := by
                  intro z
                  have h := congrArg (fun v : ↥M => (v : W'))
                    ((Representation.mem_invariants _ _).mp ha' z)
                  simpa [repRestrict_apply] using h
                have hbE : ∀ z : ↥E₀, (ρ'.comp E₀.subtype) z (N.subtype b') = N.subtype b' := by
                  intro z
                  have h := congrArg (fun v : ↥N => (v : W'))
                    ((Representation.mem_invariants _ _).mp hb' z)
                  simpa [repRestrict_apply] using h
                rw [Representation.mem_invariants]
                intro z
                rw [← hab, map_add, haE z, hbE z]
            have hbot : VM ⊓ VN = ⊥ := by
              rw [Submodule.eq_bot_iff]
              intro w hw
              obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
              have h1 : w ∈ M := hVMle hw1
              have h2 : w ∈ N := hVNle hw2
              have h3 := Submodule.mem_inf.mpr ⟨h1, h2⟩
              rw [hMNbot] at h3
              simpa using h3
            have hVMfin : Module.finrank k ↥VM = Module.finrank k ↥(Representation.invariants
                ((repRestrict ρ' M hMstab).comp E₀.subtype)) :=
              (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Submodule.subtype M)
                Subtype.coe_injective _)).symm
            have hVNfin : Module.finrank k ↥VN = Module.finrank k ↥(Representation.invariants
                ((repRestrict ρ' N hNstab).comp E₀.subtype)) :=
              (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Submodule.subtype N)
                Subtype.coe_injective _)).symm
            have hsum := Submodule.finrank_sup_add_finrank_inf_eq VM VN
            rw [hbot, show Module.finrank k ↥(⊥ : Submodule k W') = 0 from
              Module.finrank_zero_of_subsingleton, add_zero, ← hVeq] at hsum
            rw [hVMfin, hVNfin] at hsum
            exact hsum
          have hWdim : Module.finrank k W' = Module.finrank k ↥M + Module.finrank k ↥N := by
            have hsum := Submodule.finrank_sup_add_finrank_inf_eq M N
            rw [hMNtop, hMNbot, show Module.finrank k ↥(⊥ : Submodule k W') = 0 from
              Module.finrank_zero_of_subsingleton, add_zero] at hsum
            rw [← hsum, show Module.finrank k ↥(⊤ : Submodule k W') = Module.finrank k W' from
              LinearEquiv.finrank_eq Submodule.topEquiv]
          rw [hVin, hWdim, mul_add, hMcard, hNIH]

/-- Modular Frobenius fixed-point dimension formula, algebraically closed coefficient field:
for a finite Frobenius group `L = K ⋊ E` (`K ⊴ L`, `K ⊓ E = ⊥`, `K ⊔ E = ⊤`, `C_L(h) ≤ K` for
`h ∈ K^#`) with `p ∤ |L|`, and a finite-dimensional `k`-representation `ρ` of `L` (over an
algebraically closed field `k` of characteristic `p`) whose `K`-fixed space is zero, the
`E₀`-fixed space of `ρ` has dimension `dim W / |E₀|`. -/
theorem frobenius_finrank_algClosed {k : Type*} [Field k] [IsAlgClosed k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {L : Type*} [Group L] [Fintype L] {K E : Subgroup L} (hKn : K.Normal)
    (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set L) ≤ K) (hpL : ¬ p ∣ Nat.card L)
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k L W) (hfix : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (E₀ : Subgroup L) (hE₀ : E₀ ≤ E) :
    Module.finrank k ↥(Representation.invariants (ρ.comp E₀.subtype))
      = Module.finrank k W / Nat.card ↥E₀ := by
  classical
  haveI : Nonempty ↥E₀ := ⟨1⟩
  haveI : Fintype ↥E₀ := Fintype.ofFinite _
  rw [← frobenius_finrank_aux hKn hinf hsup hcent hpL E₀ hE₀ (Module.finrank k W) W rfl ρ hfix]
  exact (Nat.mul_div_cancel_left _ Nat.card_pos).symm
