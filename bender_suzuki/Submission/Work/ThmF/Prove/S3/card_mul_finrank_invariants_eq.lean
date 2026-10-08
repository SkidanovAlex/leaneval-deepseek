import Mathlib
import Submission.Work.Frobenius.Main
import Submission.Work.CharPrelim.frobenius_finrank_algClosed
import Submission.Work.CharPrelim.finrank_invariants_baseChange
import Submission.Work.Frobenius.Induced.conjChar_ne_self_of_fpf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.ThmF.Prove.S3

open Classical
open scoped Pointwise
open scoped TensorProduct
open Work.CharPrelim

noncomputable section

/-- **Modular Frobenius fixed-point dimension formula, algebraically closed field, only
`char ∤ |K|` required.**  This is `Work.CharPrelim.frobenius_finrank_aux` with the hypothesis
`p ∤ |L|` weakened to `p ∤ |K|` (so that `p` may divide `|E|`).  The complement `E` is never
averaged over; instead the orbit module `M` of a simple `K`-stable subspace `U` is split off
using the explicit `L`-equivariant retraction `∑_{e ∈ E} conjProj` onto `M`, whose well-definedness
is the directness of the Frobenius orbit (`sum_eq_zero_of_conj`). -/
theorem frobenius_finrank_algClosed_K {k : Type*} [Field k] [IsAlgClosed k] {p : ℕ}
    [Fact p.Prime] [CharP k p] {L : Type*} [Group L] [Fintype L] {K E : Subgroup L}
    (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set L) ≤ K)
    (hcopK : ¬ p ∣ Nat.card ↥K) (E₀ : Subgroup L) (hE₀ : E₀ ≤ E) (n : ℕ) :
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
  have hcardK : (Fintype.card ↥K : k) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h0 => hcopK ((CharP.cast_eq_zero_iff k p (Nat.card ↥K)).mp h0)
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
          fun v hv hsum => sum_eq_zero_of_conj (hU := hUstab) ρ' hinf hcent hcopK hsU hUK
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
        · -- The `L`-equivariant retraction onto `M` given by summing the conjugate projections.
          have hπzero : ∀ (g : ↥E), g ≠ 1 → ∀ u : ↥U, π (ρ' (g : L) (u : W')) = 0 := by
            intro g hg u
            have hgL : (g : L) ≠ (1 : L) := fun h => hg (Subtype.ext h)
            have hmap := conjProjMap_eq_zero (hU := hUstab) ρ' hinf hcent hcopK hsU hUK hπeq
              (e := (g : L)) (e' := (1 : L)) g.2 E.one_mem hgL
            have hval : (conjProj ρ' U π (1 : L) (ρ' (g : L) (u : W')) : W') = 0 := by
              have h := congrArg (fun T => (T ⟨ρ' (g : L) (u : W'), ⟨u, u.2, rfl⟩⟩ : W')) hmap
              simpa [conjProjMap] using h
            have hval2 : (π (ρ' (g : L) (u : W')) : W') = 0 := by
              rw [conjProj_apply] at hval
              simpa using hval
            exact Subtype.ext hval2
          set P : W' →ₗ[k] W' := ∑ e : ↥E, conjProj ρ' U π (e : L) with hPdef
          have hPmem : ∀ w : W', P w ∈ M := by
            intro w
            rw [hPdef, LinearMap.sum_apply]
            exact Submodule.sum_mem M (fun e _ =>
              le_orbitModule ρ' E U e (conjProj_mem ρ' U π (e : L) w))
          have hPfixU : ∀ (f : ↥E) (u : ↥U), P (ρ' (f : L) (u : W')) = ρ' (f : L) (u : W') := by
            intro f u
            rw [hPdef, LinearMap.sum_apply]
            rw [Finset.sum_eq_single f]
            · rw [conjProj_apply]
              have h1 : (ρ' (f : L)⁻¹) (ρ' (f : L) (u : W')) = (u : W') := by
                rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
              rw [h1]
              exact congrArg (fun v : ↥U => (ρ' (f : L) v : W')) (hπfix u)
            · intro g _ hgf
              rw [conjProj_apply]
              have hgfL : (g : L)⁻¹ * (f : L) ≠ 1 := by
                intro h
                apply hgf
                have h' : (g : L)⁻¹ * (f : L) = (1 : L) := h
                have : (f : L) = (g : L) := by
                  calc (f : L) = (g : L) * ((g : L)⁻¹ * (f : L)) := by group
                    _ = (g : L) * 1 := by rw [h']
                    _ = (g : L) := mul_one _
                exact Subtype.ext this.symm
              have hmem : (g : L)⁻¹ * (f : L) ∈ E :=
                E.mul_mem (E.inv_mem g.2) f.2
              have hzero : π (ρ' ((g : L)⁻¹ * (f : L)) (u : W')) = 0 :=
                hπzero ⟨(g : L)⁻¹ * (f : L), hmem⟩ (fun h => hgfL (Subtype.ext_iff.mp h)) u
              rw [← Module.End.mul_apply, ← map_mul, hzero]; simp
            · intro hf; exact absurd (Finset.mem_univ f) hf
          have hPfix : ∀ w ∈ M, P w = w := by
            intro w hw
            have hle : M ≤ LinearMap.ker (P - LinearMap.id) := by
              rw [hMdef]
              change (⨆ e : ↥E, U.map (ρ' (e : L))) ≤ LinearMap.ker (P - LinearMap.id)
              refine iSup_le (fun f => ?_)
              intro x hx
              obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
              rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
              exact hPfixU f ⟨u, hu⟩
            have h := hle hw
            rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
          have hPK : ∀ (k : L), k ∈ K → ∀ w : W', P (ρ' k w) = ρ' k (P w) := by
            intro k hk w
            rw [hPdef]
            conv_rhs => rw [LinearMap.sum_apply, map_sum]
            rw [LinearMap.sum_apply]
            exact Finset.sum_congr rfl
              (fun e _ => conjProj_equivariant (hU := hUstab) ρ' K hπeq (e : L) ⟨k, hk⟩ w)
          have hPE : ∀ (e : L), e ∈ E → ∀ w : W', P (ρ' e w) = ρ' e (P w) := by
            intro e he w
            have hconj : ∀ y : L, conjProj ρ' U π y = ρ' y * (U.subtype.comp π) * ρ' y⁻¹ := by
              intro y
              rw [conjProj]
              rfl
            have hterm : ∀ x : ↥E, ρ' e⁻¹ * conjProj ρ' U π (x : L) * ρ' e
                = conjProj ρ' U π
                    ((⟨(e : L)⁻¹ * (x : L), E.mul_mem (E.inv_mem he) x.2⟩ : ↥E) : L) := by
              intro x
              have h1 : ρ' ((e : L)⁻¹) * ρ' (x : L) = ρ' ((e : L)⁻¹ * (x : L)) := by rw [← map_mul]
              have h2 : ρ' ((x : L)⁻¹) * ρ' e = ρ' (((e : L)⁻¹ * (x : L))⁻¹) := by
                rw [← map_mul, mul_inv_rev, inv_inv]
              rw [hconj (x : L), hconj ((e : L)⁻¹ * (x : L)), ← h1, ← h2]
              simp only [mul_assoc]
            have hA : ρ' e⁻¹ * P * ρ' e = P := by
              rw [hPdef, Finset.mul_sum]
              rw [show (∑ x : ↥E, ρ' e⁻¹ * conjProj ρ' U π (x : L)) * ρ' e
                    = ∑ x : ↥E, ρ' e⁻¹ * conjProj ρ' U π (x : L) * ρ' e from Finset.sum_mul ..]
              rw [Finset.sum_congr rfl (fun x _ => hterm x)]
              exact Equiv.sum_comp (Equiv.mulLeft (⟨(e : L)⁻¹, E.inv_mem he⟩ : ↥E))
                (fun y : ↥E => conjProj ρ' U π (y : L))
            have hcancel : ∀ v : W', ρ' e (ρ' e⁻¹ v) = v := by
              intro v
              rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
            have h2 : (ρ' e⁻¹ * P * ρ' e) w = P w := by rw [hA]
            rw [Module.End.mul_apply, Module.End.mul_apply] at h2
            calc P (ρ' e w) = ρ' e (ρ' e⁻¹ (P (ρ' e w))) := (hcancel (P (ρ' e w))).symm
              _ = ρ' e (P w) := by rw [h2]
          have hPequiv : ∀ (g : L) (w : W'), P (ρ' g w) = ρ' g (P w) := by
            intro g w
            have hg : g ∈ K ⊔ E := by rw [hsup]; trivial
            obtain ⟨k, hk, e, he, hke⟩ :=
              (Subgroup.mem_sup_of_normal_left (s := K) (t := E) (x := g)).mp hg
            rw [← hke, map_mul, Module.End.mul_apply]
            rw [hPK k hk (ρ' e w), hPE e he w, Module.End.mul_apply]
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

end

/-! ## Fixed points as a kernel -/

/-- The fixed-point subspace of a representation, written as the kernel of the "difference" map
`w ↦ (t ↦ σ t w - w)`. -/
def fixedMap {k : Type*} [Field k] {T : Type*} [Group T] {W : Type*} [AddCommGroup W]
    [Module k W] (σ : Representation k T W) : W →ₗ[k] (T → W) where
  toFun w := fun t => σ t w - w
  map_add' a b := by funext t; simp only [Pi.add_apply, map_add]; abel
  map_smul' c a := by funext t; simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_sub]

lemma fixedMap_ker {k : Type*} [Field k] {T : Type*} [Group T] {W : Type*} [AddCommGroup W]
    [Module k W] (σ : Representation k T W) : (fixedMap σ).ker = σ.invariants := by
  ext w
  rw [LinearMap.mem_ker, Representation.mem_invariants]
  constructor
  · intro h t
    have h' : σ t w - w = 0 := congrFun h t
    exact sub_eq_zero.mp h'
  · intro h
    funext t
    change σ t w - w = 0
    rw [h t, sub_self]

/-- **Base change preserves the dimension of the fixed space**, with *no* coprimality hypothesis.
The fixed space is the kernel of the difference map, and kernels of finite linear systems keep
their rank under a field extension. -/
theorem finrank_invariants_baseChange_any {F : Type*} [Field F] {k : Type*} [Field k]
    [Algebra F k] {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F L V) (S : Subgroup L) [Finite ↥S] :
    Module.finrank k ↥(Representation.invariants ((repBaseChange F k ρ).comp S.subtype))
      = Module.finrank F ↥(Representation.invariants (ρ.comp S.subtype)) := by
  classical
  haveI : Fintype ↥S := Fintype.ofFinite _
  let φ := fixedMap (ρ.comp S.subtype)
  let Ψ := fixedMap ((repBaseChange F k ρ).comp S.subtype)
  have hφker : LinearMap.ker φ = Representation.invariants (ρ.comp S.subtype) := fixedMap_ker _
  have hΨker : LinearMap.ker Ψ
      = Representation.invariants ((repBaseChange F k ρ).comp S.subtype) := fixedMap_ker _
  have hΨeq : Ψ = (TensorProduct.piRight F k k (fun _ : ↥S => V)).toLinearMap.comp
      (φ.baseChange k) := by
    apply LinearMap.ext
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a v =>
        funext s
        change (repBaseChange F k ρ) (s : L) (a ⊗ₜ[F] v) - (a ⊗ₜ[F] v)
          = ((TensorProduct.piRight F k k (fun _ : ↥S => V)) ((φ.baseChange k) (a ⊗ₜ[F] v))) s
        rw [LinearMap.baseChange_tmul]
        simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
          repBaseChange_tmul_apply]
        rw [show (φ v) s = ρ ((s : ↥S) : L) v - v from rfl, TensorProduct.tmul_sub]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hker : LinearMap.ker Ψ = LinearMap.ker (φ.baseChange k) := by
    rw [hΨeq]
    ext w
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hw
      exact (TensorProduct.piRight F k k (fun _ : ↥S => V)).injective (by simpa using hw)
    · intro hw; rw [hw, map_zero]
  have hdim : Module.finrank k ↥(LinearMap.ker (φ.baseChange k)) = Module.finrank F ↥(φ.ker) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 := LinearMap.finrank_range_add_finrank_ker (φ.baseChange k)
    have h3 : Module.finrank k ↥(LinearMap.range (φ.baseChange k))
        = Module.finrank F ↥(LinearMap.range φ) := by
      rw [← range_baseChange]
      exact finrank_baseChange_submodule (LinearMap.range φ)
    have h4 : Module.finrank k (k ⊗[F] V) = Module.finrank F V := Module.finrank_baseChange
    omega
  rw [← hΨker, ← hφker, hker]
  exact hdim

/-- **The `K`-trace vanishes on the complement**, over an arbitrary field in which `|K|` is a unit.
This is the field-general form of `Work.CharPrelim.frobenius_trace_eq_zero`. -/
theorem frobenius_trace_eq_zero_field {L : Type*} [Group L] [Fintype L] {F : Type*} [Field F]
    {K E : Subgroup L} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) ≤ K)
    (hcardK : (Nat.card ↥K : F) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F L V) (hfix : Representation.invariants (ρ.comp K.subtype) = ⊥)
    {e : L} (he : e ∈ E) (he1 : e ≠ 1) : LinearMap.trace F V (ρ e) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hfpf : ∀ x ∈ (K : Set L), e * x * e⁻¹ = x → x = 1 := by
    intro x hx hfixx
    by_contra hx1
    have hxe : e * x = x * e := by
      have hh := congrArg (fun t => t * e) hfixx
      simpa [mul_assoc] using hh
    have hec : e ∈ Subgroup.centralizer ({x} : Set L) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxe
    have heK : e ∈ K := hcent x hx hx1 hec
    have hmem : e ∈ K ⊓ E := Subgroup.mem_inf.mpr ⟨heK, he⟩
    rw [hinf] at hmem
    exact he1 (Subgroup.mem_bot.mp hmem)
  have hzero : ∀ v : V, (∀ k : K, ρ (k : L) v = v) → v = 0 := by
    intro v hv
    have : v ∈ Representation.invariants (ρ.comp K.subtype) := by
      rw [Representation.mem_invariants]; exact hv
    rw [hfix] at this
    simpa using this
  have hS : ∑ k : K, ρ (k : L) = 0 := by
    ext v
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    apply hzero
    intro k'
    rw [map_sum]
    calc ∑ x : K, ρ (k' : L) (ρ (x : L) v)
        = ∑ x : K, ρ (((k' * x : K)) : L) v := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← Module.End.mul_apply, ← map_mul]
          congr 1
      _ = ∑ x : K, ρ (x : L) v :=
          Equiv.sum_comp (Equiv.mulLeft k') (fun x : K => ρ (x : L) v)
  let φ : K → K := fun k => ⟨(k : L) * (e * (k : L) * e⁻¹)⁻¹,
    K.mul_mem k.2 (K.inv_mem (hKn.conj_mem (k : L) k.2 e))⟩
  have hφval : ∀ k : K, (φ k : L) = (k : L) * (e * (k : L) * e⁻¹)⁻¹ := fun k => rfl
  have hφinj : Function.Injective φ := by
    intro k l hkl
    have hkk : (k : L) * (e * (k : L) * e⁻¹)⁻¹ =
        (l : L) * (e * (l : L) * e⁻¹)⁻¹ := by
      have := congrArg (fun t : K => (t : L)) hkl
      simpa [φ] using this
    have h6 : (e * (l : L) * e⁻¹)⁻¹ * (e * (k : L) * e⁻¹) = (l : L)⁻¹ * (k : L) := by
      have hh : (l : L)⁻¹ * ((k : L) * (e * (k : L) * e⁻¹)⁻¹) * (e * (k : L) * e⁻¹)
          = (l : L)⁻¹ * ((l : L) * (e * (l : L) * e⁻¹)⁻¹) * (e * (k : L) * e⁻¹) := by
        rw [hkk]
      simpa [mul_assoc] using hh.symm
    have h7 : e * ((l : L)⁻¹ * (k : L)) * e⁻¹ = (l : L)⁻¹ * (k : L) := by
      calc e * ((l : L)⁻¹ * (k : L)) * e⁻¹
          = (e * (l : L) * e⁻¹)⁻¹ * (e * (k : L) * e⁻¹) := by group
        _ = (l : L)⁻¹ * (k : L) := h6
    have hKmem : (l : L)⁻¹ * (k : L) ∈ K := K.mul_mem (K.inv_mem l.2) k.2
    have h1 : (l : L)⁻¹ * (k : L) = 1 := hfpf _ hKmem h7
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hSφ : ∑ k : K, ρ (φ k : L) = 0 := by
    let ψ : K ≃ K := Equiv.ofBijective φ hφinj.bijective_of_finite
    rw [show ∑ k : K, ρ (φ k : L) = ∑ k : K, ρ (ψ k : L) by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [ψ, Equiv.ofBijective_apply]]
    rw [Equiv.sum_comp ψ (fun k : K => ρ (k : L))]
    exact hS
  have hA : ∑ k : K, ρ ((k : L) * e * (k : L)⁻¹) = (∑ k : K, ρ (φ k : L)) * ρ e := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← map_mul]
    congr 1
    rw [hφval]
    group
  have hSumZero : ∑ k : K, ρ ((k : L) * e * (k : L)⁻¹) = 0 := by
    rw [hA, hSφ, zero_mul]
  have htr1 : LinearMap.trace F V (∑ k : K, ρ ((k : L) * e * (k : L)⁻¹)) = 0 := by
    rw [hSumZero, map_zero]
  have htr2 : LinearMap.trace F V (∑ k : K, ρ ((k : L) * e * (k : L)⁻¹))
      = (Fintype.card K : F) * LinearMap.trace F V (ρ e) := by
    rw [map_sum]
    rw [show (∑ k : K, LinearMap.trace F V (ρ ((k : L) * e * (k : L)⁻¹)))
        = ∑ k : K, LinearMap.trace F V (ρ e) by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hrep : ρ ((k : L) * e * (k : L)⁻¹) = ρ (k : L) * ρ e * ρ ((k : L)⁻¹) := by
        rw [map_mul ρ ((k : L) * e) ((k : L)⁻¹), map_mul ρ (k : L) e]
      rw [hrep]
      have h1 : ρ ((k : L)⁻¹) * ρ (k : L) = 1 := by
        rw [← map_mul ρ ((k : L)⁻¹) (k : L), inv_mul_cancel, map_one]
      rw [LinearMap.trace_mul_comm F (ρ (k : L) * ρ e) (ρ ((k : L)⁻¹)),
        ← mul_assoc, h1, one_mul]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmul : (Fintype.card K : F) * LinearMap.trace F V (ρ e) = 0 :=
    (htr1.symm.trans htr2).symm
  have hcard_ne : (Fintype.card K : F) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardK
  exact (mul_eq_zero.mp hmul).resolve_left hcard_ne

/-- Positive-characteristic case of `card_mul_finrank_invariants_eq`, isolated so that the
base change to an algebraic closure is elaborated in a clean context. -/
theorem card_mul_finrank_charP {L : Type*} [Group L] [Fintype L] {F : Type*} [Field F]
    {K E : Subgroup L} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) ≤ K)
    (hchar0 : ringChar F ≠ 0)
    (hchar : ∀ q : ℕ, q.Prime → (q : F) = 0 → ¬ q ∣ Nat.card ↥K)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F L V) (hfix : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (E₀ : Subgroup L) (hE₀ : E₀ ≤ E) :
    Nat.card ↥E₀ * Module.finrank F ↥(Representation.invariants (ρ.comp E₀.subtype))
      = Module.finrank F V := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_prime_of_ne_zero (R := F) hchar0⟩
  haveI : IsAlgClosed (AlgebraicClosure F) := inferInstance
  haveI : CharP (AlgebraicClosure F) (ringChar F) := inferInstance
  have hcardK : (Nat.card ↥K : F) ≠ 0 := fun h =>
    hchar (ringChar F) (CharP.char_prime_of_ne_zero (R := F) hchar0)
      ((ringChar.spec F (ringChar F)).mpr (dvd_refl _))
      ((ringChar.spec F (Nat.card ↥K)).mp h)
  have hfixk : Representation.invariants
      ((repBaseChange F (AlgebraicClosure F) ρ).comp K.subtype) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hdim := finrank_invariants_baseChange_any (k := AlgebraicClosure F) ρ K
    rw [hfix, show Module.finrank F ↥(⊥ : Submodule F V) = 0 from
      Module.finrank_zero_of_subsingleton] at hdim
    rw [(Submodule.finrank_eq_zero).mp hdim] at hw
    exact hw
  have hmain := frobenius_finrank_algClosed_K (k := AlgebraicClosure F) (p := ringChar F)
    hKn hinf hsup hcent (fun hd => hcardK ((ringChar.spec F (Nat.card ↥K)).mpr hd)) E₀ hE₀
    (Module.finrank (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] V))
    (AlgebraicClosure F ⊗[F] V) rfl (repBaseChange F (AlgebraicClosure F) ρ) hfixk
  have hfin : Module.finrank (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] V)
      = Module.finrank F V := Module.finrank_baseChange
  rw [finrank_invariants_baseChange_any ρ E₀, hfin] at hmain
  exact hmain

theorem card_mul_finrank_invariants_eq {L : Type*} [Group L] [Fintype L] {F : Type*} [Field F] {K E : Subgroup L} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤) (hKne : K ≠ ⊥) (hEne : E ≠ ⊥) (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) ≤ K) (hKsol : Group.IsSolvable ↥K) (hchar : ∀ q : ℕ, q.Prime → (q : F) = 0 → ¬ q ∣ Nat.card ↥K) {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (ρ : Representation F L V) (hfix : Representation.invariants (ρ.comp K.subtype) = ⊥) (E₀ : Subgroup L) (hE₀ : E₀ ≤ E) : Nat.card ↥E₀ * Module.finrank F ↥(Representation.invariants (ρ.comp E₀.subtype)) = Module.finrank F V := by
  classical
  haveI : Fintype ↥E₀ := Fintype.ofFinite _
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hcardK : (Nat.card ↥K : F) ≠ 0 := by
    intro h
    have hdvd : ringChar F ∣ Nat.card ↥K := (ringChar.spec F (Nat.card ↥K)).mp h
    have hne0 : Nat.card ↥K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    rcases eq_or_ne (ringChar F) 0 with h0 | h0
    · rw [h0] at hdvd
      exact hne0 (Nat.eq_zero_of_zero_dvd hdvd)
    · exact hchar (ringChar F) (CharP.char_prime_of_ne_zero (R := F) h0)
        ((ringChar.spec F (ringChar F)).mpr (dvd_refl _)) hdvd
  rcases eq_or_ne (ringChar F) 0 with hchar0 | hchar0
  · haveI : CharZero F := (CharP.ringChar_zero_iff_CharZero (R := F)).mp hchar0
    have hcardE₀ : (Nat.card ↥E₀ : F) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    haveI : Invertible (Nat.card ↥E₀ : F) :=
      IsUnit.invertible (by rw [isUnit_iff_ne_zero]; exact hcardE₀)
    have htrace := Representation.card_inv_mul_sum_char_eq_finrank (ρ.comp E₀.subtype)
    have hsum : ∑ e : ↥E₀, Representation.character (ρ.comp E₀.subtype) e = (Module.finrank F V : F) := by
      rw [Finset.sum_eq_single (1 : ↥E₀)]
      · rw [Representation.char_one]
      · intro e _ he1
        have heE : ((e : ↥E₀) : L) ∈ E := hE₀ e.2
        have he1' : ((e : ↥E₀) : L) ≠ 1 := fun h => he1 (Subtype.ext h)
        have h := frobenius_trace_eq_zero_field hKn hinf hsup hcent hcardK ρ hfix heE he1'
        simpa [Representation.character] using h
      · intro h1; exact absurd (Finset.mem_univ (1 : ↥E₀)) h1
    rw [hsum] at htrace
    have key : ((Module.finrank F V : ℕ) : F)
        = ((Nat.card ↥E₀ * Module.finrank F ↥(Representation.invariants (ρ.comp E₀.subtype)) : ℕ) : F) := by
      rw [Nat.cast_mul]
      calc ((Module.finrank F V : ℕ) : F)
          = (Nat.card ↥E₀ : F) * ((Nat.card ↥E₀ : F)⁻¹ * (Module.finrank F V : F)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hcardE₀, one_mul]
        _ = (Nat.card ↥E₀ : F)
              * (Module.finrank F ↥(Representation.invariants (ρ.comp E₀.subtype)) : F) := by
            rw [htrace]
    exact Nat.cast_injective key.symm
  · exact card_mul_finrank_charP hKn hinf hsup hcent hchar0 hchar ρ hfix E₀ hE₀

end Work.ThmF.Prove.S3
