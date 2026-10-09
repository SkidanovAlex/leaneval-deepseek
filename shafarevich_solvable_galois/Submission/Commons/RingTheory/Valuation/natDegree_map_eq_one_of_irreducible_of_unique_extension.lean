import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Valuation.LocalSubring
import Submission.Commons.RingTheory.Valuation.val_ringEquiv_eq_of_comap_eq
import Submission.Commons.RingTheory.Valuation.hasExtension_comap_of_comap_eq
import Submission.Commons.RingTheory.Valuation.ValuationSubring.isUnit_iff_val_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Degree one for an irreducible polynomial with an approximate root, under unique extension

Let `F'` be a separable closure of `F`, `V` a valuation subring of `F` whose extension `W` to
`F'` is unique (here: `W.comap` is `V` and `W` is stable under all `F`-automorphisms of `F'`).
If `g ∈ V[X]` is monic with `g.map (algebraMap V F)` irreducible over `F`, and `a ∈ V` satisfies
`g(a) ∈ m_V` and `g'(a) ∈ Vˣ`, then `(g.map (algebraMap V F)).natDegree = 1`.

The proof is a residue-field/Hensel argument that avoids any completeness assumption on `V`.
With `h = g.map (algebraMap V F)` and `H = h.map (algebraMap F F')`:

* every root of `H` lies in `W` (roots of a monic polynomial over a valuation ring are integral,
  and `W` is integrally closed in `F'`);
* the product `∏_{r ∈ H.roots} (φ a - r)` equals `H.eval (φ a)`, whose value is `< 1` because
  `g(a) ∈ m_V ⊆ m_W`; since all factors have value `≤ 1`, one root `r₀` has `v (φ a - r₀) < 1`;
* such a root is unique: if `r ≠ r'` both satisfied this, both would reduce to the same element
  of the residue field `κ = W ⧸ m_W`, making the reduction of the derivative vanish, whereas
  the reduction of `H'` at that point is the (non-zero) reduction of `g'(a)`;
* hence `r₀` is fixed by `Gal(F'/F)` (by `W`-stability and the invariance of the valuation), so
  `r₀ = algebraMap F F' c` for some `c : F`, and `h` has a root in `F`;
* an irreducible monic polynomial over a field with a root is linear.
-/

open Polynomial

namespace Commons.RingTheory.Valuation

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

theorem mem_of_eval₂_eq_zero_of_monic {L : Type*} [Field L] (W : ValuationSubring L)
    {p : Polynomial W} (hp : p.Monic) {x : L}
    (hx : Polynomial.eval₂ (algebraMap W L) x p = 0) : x ∈ W := by
  have hint : IsIntegral W x := ⟨p, hp, hx⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

theorem multiset_prod_le_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {s : Multiset Γ₀} (h : ∀ a ∈ s, a ≤ 1) : s.prod ≤ 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    have ha : a ≤ 1 := h a (Multiset.mem_cons_self a s)
    have hs : s.prod ≤ 1 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    calc a * s.prod ≤ a * 1 := mul_le_mul_right hs a
      _ = a := mul_one a
      _ ≤ 1 := ha

theorem natDegree_map_eq_one_of_irreducible_of_unique_extension {F F' : Type*} [Field F] [Field F']
    [Algebra F F'] [IsSepClosure F F'] (V : ValuationSubring F) (W : ValuationSubring F')
    (hW : W.comap (algebraMap F F') = V)
    (hstab : ∀ σ : F' ≃ₐ[F] F', W.comap (σ : F' →+* F') = W)
    (g : Polynomial V) (hg : g.Monic) (hirr : Irreducible (g.map (algebraMap V F)))
    (a : V) (ha : g.eval a ∈ IsLocalRing.maximalIdeal V)
    (hda : IsUnit (g.derivative.eval a)) :
    (g.map (algebraMap V F)).natDegree = 1 := by
  classical
  -- the inclusion  V → W
  let Φ : V →+* W :=
    { toFun := fun x => ⟨algebraMap F F' (algebraMap V F x), by
        rw [← ValuationSubring.mem_comap, hW]
        exact x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  set h : Polynomial F := g.map (algebraMap V F) with hh
  set gW : Polynomial W := g.map Φ with hgW
  set H : Polynomial F' := gW.map (algebraMap W F') with hH
  have hcomp : (algebraMap W F').comp Φ = (algebraMap F F').comp (algebraMap V F) := by
    ext x; rfl
  have hHh : H = h.map (algebraMap F F') := by
    rw [hH, hgW, hh]
    simp only [Polynomial.map_map]
    rw [hcomp]
  have hHmonic : H.Monic := (hg.map Φ).map (algebraMap W F')
  have hHne : H ≠ 0 := hHmonic.ne_zero
  have hhne : h ≠ 0 := (hg.map (algebraMap V F)).ne_zero
  have hderiv_ne : g.derivative ≠ 0 := by
    intro h0
    rw [h0] at hda
    simp at hda
  have hderiv_map_ne : h.derivative ≠ 0 := by
    have hm : h.derivative = (g.derivative).map (algebraMap V F) := by
      rw [hh, Polynomial.derivative_map]
    have hinj : Function.Injective (algebraMap V F) := by
      intro x y hxy; exact Subtype.ext hxy
    have hmap : (g.derivative).map (algebraMap V F) ≠ 0 := by
      intro hc
      exact hderiv_ne ((Polynomial.map_eq_zero_iff hinj).mp hc)
    rw [hm]
    exact hmap
  have hsep : h.Separable := (Polynomial.separable_iff_derivative_ne_zero hirr).mpr hderiv_map_ne
  haveI hF'sepclosed : IsSepClosed F' := IsSepClosure.sep_closed F
  have Hsplit : H.Splits := by
    rw [hHh]
    exact IsSepClosed.splits_of_separable _ hsep.map
  have hrootsW : ∀ r ∈ H.roots, r ∈ W := by
    intro r hr
    have hroot : H.IsRoot r := (Polynomial.mem_roots hHne).mp hr
    rw [Polynomial.IsRoot.def] at hroot
    have hev : Polynomial.eval₂ (algebraMap W F') r gW = H.eval r := by
      rw [hH]; exact (Polynomial.eval_map (algebraMap W F') r).symm
    exact mem_of_eval₂_eq_zero_of_monic W (hg.map Φ) (by rw [hev]; exact hroot)
  have hext := Commons.RingTheory.Valuation.hasExtension_comap_of_comap_eq W V hW
  have hlt_one : ∀ x : F, V.valuation x < 1 ↔ W.valuation (algebraMap F F' x) < 1 := by
    intro x
    have h2 := hext.val_isEquiv_comap.lt_one_iff_lt_one (x := x)
    rwa [Valuation.comap_apply] at h2
  -- the distinguished element in F'
  have ha'_eq : (algebraMap W F' (Φ a)) = algebraMap F F' (algebraMap V F a) := rfl
  have hHa : W.valuation (H.eval (algebraMap W F' (Φ a))) < 1 := by
    have h1 : H.eval (algebraMap W F' (Φ a)) = algebraMap F F' (algebraMap V F (g.eval a)) := by
      rw [hHh, Polynomial.eval_map, ha'_eq, Polynomial.eval₂_hom]
      congr 1
      rw [hh, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [h1]
    rw [← hlt_one (algebraMap V F (g.eval a))]
    exact (ValuationSubring.valuation_lt_one_iff V (g.eval a)).mp ha
  -- EXISTENCE of a root in the ball
  have heval_prod : H.eval (algebraMap W F' (Φ a)) =
      (H.roots.map (fun r => algebraMap W F' (Φ a) - r)).prod :=
    Polynomial.Splits.eval_eq_prod_roots_of_monic Hsplit hHmonic _
  have hHa_prod : W.valuation (H.eval (algebraMap W F' (Φ a))) =
      (H.roots.map (fun r => W.valuation (algebraMap W F' (Φ a) - r))).prod := by
    rw [heval_prod, map_multiset_prod W.valuation
      (H.roots.map (fun r => algebraMap W F' (Φ a) - r)), Multiset.map_map]
    rfl
  have hexists : ∃ r ∈ H.roots, W.valuation (algebraMap W F' (Φ a) - r) < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : W.ValueGroup) ≤
        (H.roots.map (fun r => W.valuation (algebraMap W F' (Φ a) - r))).prod := by
      refine Multiset.one_le_prod ?_
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact hcon r hr
    rw [← hHa_prod] at h1
    exact absurd h1 (not_le.mpr hHa)
  -- UNIQUENESS of a root in the ball
  have huniq : ∀ r ∈ H.roots, ∀ r' ∈ H.roots,
      W.valuation (algebraMap W F' (Φ a) - r) < 1 →
      W.valuation (algebraMap W F' (Φ a) - r') < 1 → r = r' := by
    intro r hr r' hr' hlt hlt'
    by_contra hne
    have hrW : r ∈ W := hrootsW r hr
    have hr'W : r' ∈ W := hrootsW r' hr'
    -- residue field of W
    set I : Ideal W := IsLocalRing.maximalIdeal W with hI
    set Ψ : W →+* (W ⧸ I) := Ideal.Quotient.mk I with hΨ
    set q : Polynomial (W ⧸ I) := gW.map Ψ with hq
    -- <r> - Φ a ∈ m
    have hsub_mem : (⟨r, hrW⟩ : W) - Φ a ∈ I := by
      rw [hI, ValuationSubring.valuation_lt_one_iff W]
      have hcoe : (((⟨r, hrW⟩ : W) - Φ a : W) : F') = r - algebraMap W F' (Φ a) := rfl
      rw [hcoe, show r - algebraMap W F' (Φ a) = -(algebraMap W F' (Φ a) - r) from by ring,
        Valuation.map_neg]
      exact hlt
    have hΨeq : Ψ (⟨r, hrW⟩ : W) = Ψ (Φ a) := by
      have hzero : Ψ ((⟨r, hrW⟩ : W) - Φ a) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]; exact hsub_mem
      rwa [map_sub, sub_eq_zero] at hzero
    -- the derivative at a reduces to a non-zero value
    have hqderiv : q.derivative = (gW.derivative).map Ψ := by
      rw [hq, Polynomial.derivative_map]
    have hq0 : Ψ ((gW.derivative).eval ⟨r, hrW⟩) ≠ 0 := by
      have key : Ψ ((gW.derivative).eval ⟨r, hrW⟩) =
          Polynomial.eval (Ψ (⟨r, hrW⟩ : W)) ((gW.derivative).map Ψ) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_hom (p := gW.derivative) Ψ (⟨r, hrW⟩ : W)).symm
      rw [key, hΨeq, ← hqderiv]
      have h2 : q.derivative.eval (Ψ (Φ a)) = Ψ (Φ (g.derivative.eval a)) := by
        rw [hqderiv, Polynomial.eval_map, Polynomial.eval₂_hom]
        congr 1
        rw [hgW, Polynomial.derivative_map, Polynomial.eval_map]
        exact Polynomial.eval₂_at_apply (p := g.derivative) Φ a
      rw [h2]
      exact (IsUnit.map Ψ (IsUnit.map Φ hda)).ne_zero
    have hunit : IsUnit ((gW.derivative).eval ⟨r, hrW⟩) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have hmemI : (gW.derivative).eval ⟨r, hrW⟩ ∈ I := by rw [hI]; exact hmem
      exact hq0 (by rw [hΨ]; exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmemI)
    have hvH' : W.valuation (H.derivative.eval r) = 1 := by
      have h1 : H.derivative.eval r =
          algebraMap W F' (Polynomial.eval (⟨r, hrW⟩ : W) (Polynomial.derivative gW)) := by
        have hd : H.derivative = (gW.derivative).map (algebraMap W F') := by
          rw [hH, Polynomial.derivative_map]
        rw [hd, ← Polynomial.eval₂_eq_eval_map]
        exact Polynomial.eval₂_hom (p := gW.derivative) (algebraMap W F') (⟨r, hrW⟩ : W)
      rw [h1]
      exact (Commons.RingTheory.Valuation.ValuationSubring.isUnit_iff_val_eq_one W _).mp hunit
    -- the derivative product
    have hderivprod : W.valuation (H.derivative.eval r) =
        ((H.roots.erase r).map (fun ρ => W.valuation (r - ρ))).prod := by
      have hfac : H = (H.roots.map (fun ρ => X - C ρ)).prod :=
        Polynomial.Splits.eq_prod_roots_of_monic Hsplit hHmonic
      have hid : H.derivative.eval r = ((H.roots.erase r).map (fun ρ => r - ρ)).prod := by
        conv_lhs => rw [hfac]
        exact Polynomial.eval_multiset_prod_X_sub_C_derivative hr
      rw [hid, map_multiset_prod W.valuation ((H.roots.erase r).map (fun ρ => r - ρ)),
        Multiset.map_map]
      rfl
    -- the product is bounded by the r'-factor
    have hle : ((H.roots.erase r).map (fun ρ => W.valuation (r - ρ))).prod
        ≤ W.valuation (r - r') := by
      have hmem : r' ∈ H.roots.erase r := (Multiset.mem_erase_of_ne (Ne.symm hne)).mpr hr'
      have hsplit : (H.roots.erase r).map (fun ρ => W.valuation (r - ρ)) =
          W.valuation (r - r') ::ₘ
            (((H.roots.erase r).erase r').map (fun ρ => W.valuation (r - ρ))) := by
        have hstep := congrArg (Multiset.map (fun ρ => W.valuation (r - ρ)))
          (Multiset.cons_erase hmem)
        rw [Multiset.map_cons] at hstep
        exact hstep.symm
      rw [hsplit, Multiset.prod_cons]
      have hrest : (((H.roots.erase r).erase r').map
          (fun ρ => W.valuation (r - ρ))).prod ≤ 1 := by
        refine multiset_prod_le_one ?_
        intro x hx
        obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hx
        have hρroots : ρ ∈ H.roots :=
          Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hρ)
        calc W.valuation (r - ρ) ≤ max (W.valuation r) (W.valuation ρ) :=
              Valuation.map_sub _ _ _
          _ ≤ 1 := max_le ((ValuationSubring.valuation_le_one_iff W r).mpr hrW)
                          ((ValuationSubring.valuation_le_one_iff W ρ).mpr (hrootsW ρ hρroots))
      calc W.valuation (r - r') * _ ≤ W.valuation (r - r') * 1 := mul_le_mul_right hrest _
        _ = W.valuation (r - r') := mul_one _
    have hrr' : W.valuation (r - r') < 1 := by
      have hra : W.valuation (r - algebraMap W F' (Φ a)) < 1 := by
        rw [show r - algebraMap W F' (Φ a) = -(algebraMap W F' (Φ a) - r) from by ring,
          Valuation.map_neg]
        exact hlt
      have hr'a : W.valuation (r' - algebraMap W F' (Φ a)) < 1 := by
        rw [show r' - algebraMap W F' (Φ a) = -(algebraMap W F' (Φ a) - r') from by ring,
          Valuation.map_neg]
        exact hlt'
      have h1 : r - r' = (r - algebraMap W F' (Φ a)) - (r' - algebraMap W F' (Φ a)) := by ring
      rw [h1]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hra hr'a)
    have hcontra : W.valuation (H.derivative.eval r) < 1 := by
      rw [hderivprod]
      exact lt_of_le_of_lt hle hrr'
    rw [hvH'] at hcontra
    exact lt_irrefl 1 hcontra
  -- Galois invariance
  obtain ⟨r0, hr0mem, hr0lt⟩ := hexists
  have hr0eq : ∀ r ∈ H.roots, W.valuation (algebraMap W F' (Φ a) - r) < 1 → r = r0 :=
    fun r hr hlt => huniq r hr r0 hr0mem hlt hr0lt
  have hval_inv : ∀ (σ : F' ≃ₐ[F] F') (y : F'), W.valuation (σ y) = W.valuation y := by
    intro σ y
    exact Commons.RingTheory.Valuation.val_ringEquiv_eq_of_comap_eq
      (Algebra.IsSeparable.isAlgebraic F F') W σ.toRingEquiv (fun c => σ.commutes c) (hstab σ) y
  have hfixed : ∀ σ : F' ≃ₐ[F] F', σ r0 = r0 := by
    intro σ
    have hr0root : H.eval r0 = 0 :=
      (Polynomial.IsRoot.def).mp ((Polynomial.mem_roots hHne).mp hr0mem)
    have hroot : H.eval (σ r0) = 0 := by
      have hHx : H.eval (σ r0) = σ (H.eval r0) := by
        have hae := Polynomial.aeval_algHom_apply σ r0 h
        rw [Polynomial.aeval_def, Polynomial.aeval_def] at hae
        rw [hHh, Polynomial.eval_map, Polynomial.eval_map]
        exact hae
      rw [hHx, hr0root, map_zero]
    have hmem : σ r0 ∈ H.roots :=
      (Polynomial.mem_roots hHne).mpr ((Polynomial.IsRoot.def).mpr hroot)
    have hfixa : σ (algebraMap W F' (Φ a)) = algebraMap W F' (Φ a) := by
      have hcoe : algebraMap W F' (Φ a) = algebraMap F F' (algebraMap V F a) := rfl
      rw [hcoe, AlgEquiv.commutes]
    have hltσ : W.valuation (algebraMap W F' (Φ a) - σ r0) < 1 := by
      have h1 : algebraMap W F' (Φ a) - σ r0 = σ (algebraMap W F' (Φ a) - r0) := by
        rw [map_sub, hfixa]
      rw [h1, hval_inv]
      exact hr0lt
    exact hr0eq (σ r0) hmem hltσ
  -- r0 comes from F
  have hrange : r0 ∈ Set.range (algebraMap F F') :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed r0).mpr hfixed
  obtain ⟨c, hc⟩ := hrange
  have hr0root : H.eval r0 = 0 :=
    (Polynomial.IsRoot.def).mp ((Polynomial.mem_roots hHne).mp hr0mem)
  have hcroot : h.eval c = 0 := by
    have h1 : H.eval (algebraMap F F' c) = algebraMap F F' (h.eval c) := by
      rw [hHh, Polynomial.eval_map, Polynomial.eval₂_hom]
    have h2 : H.eval (algebraMap F F' c) = 0 := by rw [hc]; exact hr0root
    have h3 : algebraMap F F' (h.eval c) = 0 := by rw [← h1]; exact h2
    exact (algebraMap F F').injective (by rw [h3, map_zero])
  -- conclude degree 1
  have hdiv : (X - C c) ∣ h := (Polynomial.dvd_iff_isRoot).mpr ((Polynomial.IsRoot.def).mpr hcroot)
  obtain ⟨q', hq'⟩ := hdiv
  have hXC_ne : (X - C c : Polynomial F) ≠ 0 := (Polynomial.monic_X_sub_C c).ne_zero
  have hq'_ne : q' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq'
    exact hhne hq'
  have hunit : IsUnit q' := by
    rcases hirr.isUnit_or_isUnit hq' with h1 | h1
    · exfalso
      have := Polynomial.natDegree_eq_zero_of_isUnit h1
      rw [Polynomial.natDegree_X_sub_C] at this
      exact one_ne_zero this
    · exact h1
  show h.natDegree = 1
  rw [hq', Polynomial.natDegree_mul hXC_ne hq'_ne,
    Polynomial.natDegree_eq_zero_of_isUnit hunit, Polynomial.natDegree_X_sub_C]


end Commons.RingTheory.Valuation