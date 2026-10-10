import Mathlib.Computability.Reduce
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open CategoryTheory

namespace Commons.RepresentationTheory.TateCohomology

theorem subsingleton_tateCohomology_coind_bot {G : Type} [Group G] [Fintype G]
    (W : Rep ℤ (⊥ : Subgroup G)) (r : ℤ) :
    Subsingleton (tateCohomology (Rep.coind (⊥ : Subgroup G).subtype W) r) := by
  classical
  let M : Rep ℤ G := Rep.coind (⊥ : Subgroup G).subtype W
  change Subsingleton (tateCohomology M r)
  by_cases hr1 : 1 ≤ r
  · -- r ≥ 1 : use the isomorphism with group cohomology and Shapiro's lemma
    set n := r.toNat with hn
    have hnz : n ≠ 0 := by omega
    have hnr : (n : ℤ) = r := by omega
    haveI : NeZero n := ⟨hnz⟩
    haveI hsub : Subsingleton (groupCohomology M n) := by
      have h := Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot
        (G := G) W (n - 1)
      rw [show n = (n - 1) + 1 from (Nat.succ_pred_eq_of_pos (by omega)).symm]
      exact h
    have e : tateCohomology M (n : ℤ) ≅ groupCohomology M n :=
      (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) n).app M
    rw [← hnr]
    exact e.toLinearEquiv.injective.subsingleton
  · have hr1' : r ≤ 0 := by omega
    by_cases hr2 : r ≤ -2
    · -- r ≤ -2 : use the isomorphism with group homology, ind = coind, and Shapiro
      set n := (-r).toNat - 1 with hn
      have hn_pos : 0 < n := by omega
      have hmn : r = -((n : ℤ) + 1) := by omega
      haveI : NeZero n := ⟨by omega⟩
      haveI hsub : Subsingleton (groupHomology M n) := by
        classical
        haveI hbot : Subsingleton (⊥ : Subgroup G) :=
          ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
        haveI : (⊥ : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
        have ei : M ≅ Rep.ind (⊥ : Subgroup G).subtype W := (Rep.indCoindIso W).symm
        have h1 : groupHomology M n ≅
            groupHomology (Rep.ind (⊥ : Subgroup G).subtype W) n := by
          simpa only [groupHomology.functor_obj] using (groupHomology.functor ℤ G n).mapIso ei
        have h2 : groupHomology (Rep.ind (⊥ : Subgroup G).subtype W) n ≅ groupHomology W n :=
          groupHomology.indIso (⊥ : Subgroup G) W n
        haveI h3 : Subsingleton (groupHomology W n) := by
          have hz : Limits.IsZero (groupHomology W ((n - 1) + 1)) :=
            isZero_groupHomology_succ_of_subsingleton W (n - 1)
          rw [show n = (n - 1) + 1 from (Nat.succ_pred_eq_of_pos hn_pos).symm]
          exact ModuleCat.subsingleton_of_isZero hz
        exact (h1.trans h2).toLinearEquiv.injective.subsingleton
      have e : tateCohomology M r ≅ groupHomology M n :=
        (TateCohomology.isoGroupHomology (R := ℤ) (G := G) r n hmn).app M
      exact e.toLinearEquiv.injective.subsingleton
    · -- r = 0 or r = -1 : explicit low degree computation
      have hr01 : r = 0 ∨ r = -1 := by omega
      rcases hr01 with h0 | h1
      · -- r = 0
        subst r
        letI : Module ℤ M.V := M.hV2
        let inv := M.ρ.invariants
        letI : Module ℤ ↥inv := inv.module
        let nrm := M.ρ.norm
        have key (g x : G) (f : M.V) :
            (↑(M.ρ g f) : G → W.V) x = (↑f : G → W.V) (x * g) := rfl
        obtain ⟨e⟩ := @Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
          G M.V _ _ M.hV1 M.hV2 M.ρ
        let p := Submodule.comap inv.subtype (LinearMap.range nrm)
        have htop : p = ⊤ := by
          rw [Submodule.eq_top_iff']
          intro x
          rw [Submodule.mem_comap]
          set w : W.V := (↑(x : M.V) : G → W.V) 1 with hw
          let f : M.V := ⟨fun y => if y = 1 then w else 0, by
            rw [Representation.mem_coindV]
            intro g h
            have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
            have hg' : g = 1 := Subtype.ext hg
            subst hg'
            simp⟩
          refine ⟨f, ?_⟩
          have hx : ∀ g : G, M.ρ g (x : M.V) = (x : M.V) :=
            (Representation.mem_invariants M.ρ (x : M.V)).mp x.2
          have hconst : ∀ y : G, (↑(x : M.V) : G → W.V) y = w := by
            intro y
            have h := congrArg (fun z : M.V => (↑z : G → W.V) 1) (hx y)
            rw [key] at h
            simpa [hw, mul_one] using h
          show nrm f = (x : M.V)
          apply Subtype.ext
          funext y
          have hnorm : (↑(nrm f) : G → W.V) y = w := by
            show (↑(M.ρ.norm f) : G → W.V) y = w
            rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
            have hterm : ∀ g : G,
                (↑(M.ρ g f) : G → W.V) y = (if y * g = 1 then w else 0) := by
              intro g
              rw [key]
            simp only [hterm]
            rw [Finset.sum_eq_single y⁻¹]
            · simp
            · intro b _ hb
              rw [if_neg]
              intro hcon
              exact hb (inv_eq_of_mul_eq_one_right hcon).symm
            · simp
          rw [hnorm, hconst y]
        rw [Equiv.subsingleton_congr (LinearEquiv.toEquiv e)]
        rw [Submodule.Quotient.subsingleton_iff]
        exact htop
      · -- r = -1
        subst r
        letI : Module ℤ M.V := M.hV2
        let nrm := M.ρ.norm
        let K := LinearMap.ker nrm
        letI : Module ℤ ↥K := K.module
        let S := Submodule.span ℤ (Set.range fun p : G × M.V => M.ρ p.1 p.2 - p.2)
        letI : Module ℤ ↥(S : Submodule ℤ M.V) := S.module
        have key (g x : G) (f : M.V) :
            (↑(M.ρ g f) : G → W.V) x = (↑f : G → W.V) (x * g) := rfl
        obtain ⟨e⟩ := @Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso
          G M.V _ _ M.hV1 M.hV2 M.ρ
        let p := Submodule.comap K.subtype S
        have hp : p = ⊤ := by
          rw [Submodule.eq_top_iff']
          intro x
          rw [Submodule.mem_comap]
          have hker : nrm (x : M.V) = 0 := LinearMap.mem_ker.mp x.2
          have hx0 : ∑ b : G, ((x : M.V) : G → W.V) b = 0 := by
            have h1 : (↑(nrm (x : M.V)) : G → W.V) 1 = 0 := by rw [hker]; rfl
            have h2 : (↑(nrm (x : M.V)) : G → W.V) 1
                = ∑ b : G, ((x : M.V) : G → W.V) b := by
              show (↑(M.ρ.norm (x : M.V)) : G → W.V) 1 = _
              rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
              refine Finset.sum_congr rfl (fun b _ => ?_)
              rw [key, one_mul]
            rw [h2] at h1
            exact h1
          let delta : G → W.V → M.V := fun b z => ⟨fun y => if y = b then z else 0, by
            rw [Representation.mem_coindV]
            intro g h
            have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
            have hg' : g = 1 := Subtype.ext hg
            subst hg'
            simp⟩
          have hdelta_apply (b y : G) (z : W.V) :
              (↑(delta b z) : G → W.V) y = if y = b then z else 0 := rfl
          have hdelta_rho (b : G) (z : W.V) : M.ρ b⁻¹ (delta 1 z) = delta b z := by
            apply Subtype.ext; funext y
            rw [key, hdelta_apply, hdelta_apply]
            simp [mul_inv_eq_one]
          have hdelta_mem (b : G) (z : W.V) : delta b z - delta 1 z ∈ S := by
            have hmem : M.ρ b⁻¹ (delta 1 z) - delta 1 z ∈ S :=
              Submodule.subset_span ⟨(b⁻¹, delta 1 z), rfl⟩
            rwa [hdelta_rho] at hmem
          have hdecomp : (x : M.V)
              = ∑ b : G, (delta b (((x : M.V) : G → W.V) b)
                  - delta 1 (((x : M.V) : G → W.V) b)) := by
            apply Subtype.ext; funext y
            rw [Submodule.coe_sum, Finset.sum_apply]
            rw [show (∑ b : G, (↑(delta b (((x : M.V) : G → W.V) b)
                    - delta 1 (((x : M.V) : G → W.V) b)) : G → W.V) y)
                = ∑ b : G, ((if y = b then ((x : M.V) : G → W.V) b else 0)
                    - (if y = 1 then ((x : M.V) : G → W.V) b else 0)) from by
              refine Finset.sum_congr rfl (fun b _ => ?_)
              rw [Submodule.coe_sub, Pi.sub_apply, hdelta_apply, hdelta_apply]]
            rw [Finset.sum_sub_distrib]
            have hfirst : ∑ b : G, (if y = b then ((x : M.V) : G → W.V) b else 0)
                = ((x : M.V) : G → W.V) y := by
              rw [Finset.sum_eq_single y]
              · simp
              · intro b _ hb; rw [if_neg (Ne.symm hb)]
              · simp
            have hsecond : ∑ b : G, (if y = 1 then ((x : M.V) : G → W.V) b else 0) = 0 := by
              by_cases hy : y = 1
              · subst hy; simpa using hx0
              · simp [hy]
            rw [hfirst, hsecond, sub_zero]
          change (x : M.V) ∈ S
          rw [hdecomp]
          exact Submodule.sum_mem _ (fun b _ => hdelta_mem b _)
        rw [Equiv.subsingleton_congr (LinearEquiv.toEquiv e)]
        rw [Submodule.Quotient.subsingleton_iff]
        exact hp

end Commons.RepresentationTheory.TateCohomology