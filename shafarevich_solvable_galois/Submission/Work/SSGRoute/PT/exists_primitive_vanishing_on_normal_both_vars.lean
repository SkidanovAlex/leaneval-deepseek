import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.PT.isCoboundaryOn_top_of_isProPrimeToP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Killing a `2`-cocycle on `Γ × V` **and** on `V × Γ`

Let `Γ` be a compact topological group, `V ⊴ Γ` a closed normal pro-prime-to-`p` subgroup and
`c` a locally constant `2`-cocycle with values in a finite `𝔽_p`-module `N` which already vanishes
on `Γ × V` (`hvan`).  Then `c` is the coboundary of a locally constant `1`-cochain `u` which kills
it on `V × Γ` as well:

* `Work.SSGRoute.PT.exists_primitive_vanishing_on_normal_both_vars`.

This is the cochain-level `H¹(V,N) = 0` step of the inflation–restriction sequence: `H¹` of the
pro-prime-to-`p` group `V` vanishes with finite `𝔽_p`-coefficients
(`Work.SSGRoute.PT.isCoboundaryOn_top_of_isProPrimeToP`), so the failure of `c` to be right-`V`-
invariant in its first variable can be corrected.  The correction is chosen on the quotient
`Γ ⧸ (V ⊔ W)`, where `W` is an open normal subgroup both fixing `c` and acting trivially on `N`,
which makes it locally constant by construction.
-/

namespace Work.SSGRoute.PT

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

theorem exists_primitive_vanishing_on_normal_both_vars
    (p : ℕ) [Fact p.Prime] {Γ N : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction Γ N]
    [SMulCommClass Γ (ZMod p) N] [Finite N]
    (V : Subgroup Γ) (hVn : V.Normal) (hVclosed : IsClosed (V : Set Γ))
    (hVpro : Work.SSGRoute.IsProPrimeToP p ↥V)
    (hker : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ ∀ g ∈ U₀, ∀ n : N, g • n = n)
    (c : Γ → Γ → N) (hc : SSGRoute.IsCocycle2 (MonoidHom.id Γ) c)
    (hlc : SSGRoute.IsLocConst2 c) (hvan : ∀ g : Γ, ∀ v ∈ V, c g v = 0) :
    ∃ u : Γ → N, SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) u ∧
      (∀ g : Γ, ∀ v ∈ V, c g v = g • u v - u (g * v) + u g) ∧
      (∀ v ∈ V, ∀ h : Γ, c v h = v • u h - u (v * h) + u v) := by
  classical
  haveI hVnI : V.Normal := hVn
  -- ## Step 1: `c` is right-`V`-invariant in its second variable
  have hinv2 : ∀ g h : Γ, ∀ v ∈ V, c g (h * v) = c g h := by
    intro g h v hv
    have h1 := hc g h v
    simp only [MonoidHom.id_apply] at h1
    rw [hvan h v hv, hvan (g * h) v hv] at h1
    have h2 : c g (h * v) - c g h = 0 := by simpa using h1
    exact sub_eq_zero.mp h2
  -- ## Step 2: `v ↦ c v h` is a `1`-cocycle on `V`
  have hpsi : ∀ h : Γ, ∀ v ∈ V, ∀ w ∈ V, c (v * w) h = v • c w h + c v h := by
    intro h v hv w hw
    have h1 := hc v w h
    simp only [MonoidHom.id_apply] at h1
    have hvw : c v (w * h) = c v h := by
      have h2 : w * h = h * (h⁻¹ * w * h) := by group
      rw [h2, hinv2 v h (h⁻¹ * w * h) (by simpa using hVnI.conj_mem w hw h⁻¹)]
    rw [hvan v w hw, hvw] at h1
    have h3 : v • c w h - c (v * w) h + c v h = 0 := by simpa using h1
    have h4 : v • c w h + c v h - c (v * w) h = 0 := by rw [← h3]; abel
    exact (sub_eq_zero.mp h4).symm
  -- ## Step 3: the local constancy data
  obtain ⟨U, hUopen, hUinv⟩ := hlc
  obtain ⟨U₀, hU₀open, hU₀triv⟩ := hker
  have hKopen : IsOpen (((U ⊓ U₀ : Subgroup Γ)) : Set Γ) := by
    rw [Subgroup.coe_inf]; exact hUopen.inter hU₀open
  have hKclosed : IsClosed (((U ⊓ U₀ : Subgroup Γ)) : Set Γ) :=
    Subgroup.isClosed_of_isOpen _ hKopen
  set W : Subgroup Γ := (U ⊓ U₀).normalCore with hW
  haveI hWn : W.Normal := by rw [hW]; exact Subgroup.normalCore_normal _
  have hWle : W ≤ U ⊓ U₀ := by rw [hW]; exact Subgroup.normalCore_le _
  have hWclosed : IsClosed (W : Set Γ) := by
    rw [hW]; exact Subgroup.normalCore_isClosed _ hKclosed
  haveI hKfin : (U ⊓ U₀).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Subgroup.quotient_finite_of_isOpen _ hKopen
  haveI hWfin : W.FiniteIndex := by rw [hW]; infer_instance
  have hWopen : IsOpen (W : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex W hWclosed
  have hWinv1 : ∀ g h : Γ, ∀ w ∈ W, c (g * w) h = c g h := by
    intro g h w hw
    have h1 := hUinv g h w 1 (hWle hw).1 U.one_mem
    simpa using h1
  have hWinv2 : ∀ g h : Γ, ∀ w ∈ W, c g (h * w) = c g h := by
    intro g h w hw
    have h1 := hUinv g h 1 w U.one_mem (hWle hw).1
    simpa using h1
  -- ## Step 4: right-`(V ⊔ W)`-invariance in the second variable
  have hVWinv2 : ∀ g h : Γ, ∀ k ∈ (V ⊔ W : Subgroup Γ), c g (h * k) = c g h := by
    intro g
    have hle : V ⊔ W ≤
        ({ carrier := {k : Γ | ∀ h : Γ, c g (h * k) = c g h},
           mul_mem' := by
             intro a b ha hb h
             rw [← mul_assoc, hb, ha]
           one_mem' := by intro h; rw [mul_one]
           inv_mem' := by
             intro a ha h
             have h2 : (h * a⁻¹) * a = h := by group
             have h1 := ha (h * a⁻¹)
             rw [h2] at h1
             exact h1.symm } : Subgroup Γ) := by
      apply sup_le
      · intro v hv h; exact hinv2 g h v hv
      · intro w hw h; exact hWinv2 g h w hw
    intro h k hk
    exact hle hk h
  -- ## Step 5: solutions of `v • m - m = c v (out q)` for every class `q`
  set VW : Subgroup Γ := V ⊔ W with hVW
  haveI hVWn : VW.Normal := by rw [hVW]; exact Subgroup.sup_normal V W
  have hVleVW : V ≤ VW := by rw [hVW]; exact le_sup_left
  have hWleVW : W ≤ VW := by rw [hVW]; exact le_sup_right
  have hVWinv2' : ∀ g h : Γ, ∀ k ∈ VW, c g (h * k) = c g h := hVWinv2
  have hkerV : ∃ U' : Subgroup ↥V, IsOpen (U' : Set ↥V) ∧ ∀ g ∈ U', ∀ n : N, g • n = n := by
    refine ⟨U₀.comap V.subtype, ?_, ?_⟩
    · exact hU₀open.preimage continuous_subtype_val
    · intro g hg n
      exact hU₀triv (g : Γ) hg n
  have hsol : ∀ q : Γ ⧸ VW, ∃ m : N,
      ∀ v : ↥V, c (v : Γ) (Quotient.out q) = (v : Γ) • m - m := by
    intro q
    haveI : CompactSpace ↥V := isCompact_iff_compactSpace.mp hVclosed.isCompact
    let ψ : ↥V → N := fun v => c (v : Γ) (Quotient.out q)
    have hcoc : SSGRoute.IsCocycleOn (MonoidHom.id ↥V) ⊤ ψ := by
      intro g _ w _
      show c ((g * w : ↥V) : Γ) (Quotient.out q)
        = c (g : Γ) (Quotient.out q) + (g : Γ) • c (w : Γ) (Quotient.out q)
      have h1 := hpsi (Quotient.out q) (g : Γ) g.2 (w : Γ) w.2
      rw [show ((g * w : ↥V) : Γ) = (g : Γ) * (w : Γ) from rfl, h1]
      abel
    have hloc : SSGRoute.IsLocConstOn (⊤ : Subgroup ↥V) ψ := by
      refine ⟨U.comap V.subtype, hUopen.preimage continuous_subtype_val, ?_⟩
      intro g _ x hx _
      show c ((g * x : ↥V) : Γ) (Quotient.out q) = c (g : Γ) (Quotient.out q)
      rw [show ((g * x : ↥V) : Γ) = (g : Γ) * (x : Γ) from rfl]
      have h1 := hUinv (g : Γ) (Quotient.out q) (x : Γ) 1 hx U.one_mem
      simpa using h1
    obtain ⟨m, hm⟩ := isCoboundaryOn_top_of_isProPrimeToP p (Γ := ↥V) (N := N)
      hVpro hkerV ψ hcoc hloc
    exact ⟨m, fun v => hm v (Subgroup.mem_top v)⟩
  -- ## Step 6: the canonical choice, adapted to the class of `1`
  let νbar : Γ ⧸ VW → N := fun q => if q = 1 then 0 else Classical.choose (hsol q)
  have hνbar_one : νbar 1 = 0 := by simp [νbar]
  have hνbar : ∀ q : Γ ⧸ VW, ∀ v : ↥V,
      c (v : Γ) (Quotient.out q) = (v : Γ) • νbar q - νbar q := by
    intro q v
    by_cases hq : q = 1
    · subst hq
      rw [hνbar_one]
      have hmem : Quotient.out (1 : Γ ⧸ VW) ∈ VW :=
        (QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' (1 : Γ ⧸ VW))
      have h1 : c (v : Γ) (Quotient.out (1 : Γ ⧸ VW)) = c (v : Γ) 1 := by
        have h2 := hVWinv2' (v : Γ) 1 (Quotient.out (1 : Γ ⧸ VW)) hmem
        simpa using h2
      rw [h1, hvan (v : Γ) 1 V.one_mem]
      simp
    · rw [show νbar q = Classical.choose (hsol q) from by simp [νbar, hq]]
      exact Classical.choose_spec (hsol q) v
  -- ## Step 7: the correction
  let u : Γ → N := fun g => νbar (QuotientGroup.mk' VW g)
  refine ⟨u, ?_, ?_, ?_⟩
  · -- local constancy: `u` is right-`W`-invariant
    refine ⟨W, hWopen, ?_⟩
    intro g _ x hx _
    show u (g * x) = u g
    show νbar (QuotientGroup.mk' VW (g * x)) = νbar (QuotientGroup.mk' VW g)
    rw [map_mul, show QuotientGroup.mk' VW x = 1 from
      (QuotientGroup.eq_one_iff x).mpr (hWleVW hx), mul_one]
  · -- vanishing on `Γ × V`
    intro g v hv
    have hv1 : QuotientGroup.mk' VW v = 1 :=
      (QuotientGroup.eq_one_iff v).mpr (hVleVW hv)
    have hgv : QuotientGroup.mk' VW (g * v) = QuotientGroup.mk' VW g := by
      rw [map_mul, hv1, mul_one]
    have hu1 : u g = νbar (QuotientGroup.mk' VW g) := rfl
    have hu2 : u (g * v) = νbar (QuotientGroup.mk' VW g) := by
      show νbar (QuotientGroup.mk' VW (g * v)) = νbar (QuotientGroup.mk' VW g)
      rw [hgv]
    have hu3 : u v = 0 := by
      show νbar (QuotientGroup.mk' VW v) = 0
      rw [hv1, hνbar_one]
    show c g v = g • u v - u (g * v) + u g
    rw [hu3, hu2, hu1, hvan g v hv]
    simp
  · -- vanishing on `V × Γ`
    intro v hv h
    have hv1 : QuotientGroup.mk' VW v = 1 :=
      (QuotientGroup.eq_one_iff v).mpr (hVleVW hv)
    have hvh : QuotientGroup.mk' VW (v * h) = QuotientGroup.mk' VW h := by
      rw [map_mul, hv1, one_mul]
    have hrep : c v h = c v (Quotient.out (QuotientGroup.mk' VW h)) := by
      let q : Γ ⧸ VW := QuotientGroup.mk' VW h
      have hq : q = QuotientGroup.mk' VW h := rfl
      have hmem : h⁻¹ * Quotient.out q ∈ VW := (QuotientGroup.eq).mp (by
        have h1 : ((Quotient.out q : Γ) : Γ ⧸ VW) = (h : Γ ⧸ VW) := by
          rw [QuotientGroup.out_eq', hq, QuotientGroup.mk'_apply]
        exact h1.symm)
      have h2 : h * (h⁻¹ * Quotient.out q) = Quotient.out q := by group
      have h3 := hVWinv2' v h (h⁻¹ * Quotient.out q) hmem
      rw [h2] at h3
      exact h3.symm
    have hu1 : u h = νbar (QuotientGroup.mk' VW h) := rfl
    have hu2 : u (v * h) = νbar (QuotientGroup.mk' VW h) := by
      show νbar (QuotientGroup.mk' VW (v * h)) = νbar (QuotientGroup.mk' VW h)
      rw [hvh]
    have hu3 : u v = 0 := by
      show νbar (QuotientGroup.mk' VW v) = 0
      rw [hv1, hνbar_one]
    show c v h = v • u h - u (v * h) + u v
    rw [hrep, hu1, hu2, hu3, add_zero]
    exact hνbar (QuotientGroup.mk' VW h) ⟨v, hv⟩

end Work.SSGRoute.PT
