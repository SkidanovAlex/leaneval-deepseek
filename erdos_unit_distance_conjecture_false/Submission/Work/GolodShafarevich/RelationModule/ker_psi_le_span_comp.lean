import Mathlib
import Submission.Work.GolodShafarevich.Setup
import Submission.Work.GolodShafarevich.RelationModule.Defs

/-!
# Descent of the relation-module statement along an injective group homomorphism

If `ι : H →* G` is injective and `ker ψ_f` is spanned by the derivative vectors of
relators `R`, then `ker ψ_{ι ∘ f}` is spanned by the corresponding vectors for `ι ∘ f`.

The group algebra `k[G]` splits as a direct sum over the left cosets of `ι(H)`,
each of which is a copy of `k[H]`; this splitting (together with the naturality of
`Vfun` and `gGenSubOne`) does the job.
-/

open scoped MonoidAlgebra

namespace Work.GolodShafarevich.RelationModule

open Work.GolodShafarevich

/-! ## Coset decomposition of `k[G]` along an injective `ι : H →* G` -/

section Coset

variable {k : Type*} [CommRing k]

variable {G H : Type*} [Group G] [Group H] (ι : H →* G)

/-- The parametrization `h ↦ t * ι h` of the left coset `t · ι(H)`. -/
abbrev cMap (t : G) : H → G := fun h => t * ι h

theorem cMap_injective (hι : Function.Injective ι) (t : G) : Function.Injective (cMap ι t) :=
  fun _ _ hab => hι (mul_left_cancel hab)

theorem mk_cMap (t : G) (h : H) :
    (QuotientGroup.mk (cMap ι t h) : G ⧸ ι.range) = QuotientGroup.mk t :=
  QuotientGroup.mk_mul_of_mem t ⟨h, rfl⟩

/-- Push `k[H]` into the coset `t·ι(H)` of `k[G]`. -/
noncomputable def iota (t : G) : MonoidAlgebra k H →+ MonoidAlgebra k G where
  toFun z := MonoidAlgebra.mapDomain (cMap ι t) z
  map_zero' := MonoidAlgebra.mapDomain_zero _
  map_add' x y := MonoidAlgebra.mapDomain_add _ x y

@[simp]
theorem iota_apply_eq (t : G) (z : MonoidAlgebra k H) :
    iota ι t z = MonoidAlgebra.mapDomain (cMap ι t) z := rfl

/-- The value of `iota t z` on the coset `t·ι(H)`. -/
theorem iota_apply_self (hι : Function.Injective ι) (t : G) (z : MonoidAlgebra k H) (h : H) :
    (iota ι t z).coeff (cMap ι t h) = z.coeff h :=
  Finsupp.mapDomain_apply_of_injective (cMap_injective ι hι t) z.coeff h

/-- Read off the coefficients of `x` on the coset `t·ι(H)`, as an element of `k[H]`. -/
noncomputable def pi (hι : Function.Injective ι) (t : G) :
    MonoidAlgebra k G →+ MonoidAlgebra k H where
  toFun x := MonoidAlgebra.comapDomain (cMap ι t) (cMap_injective ι hι t) x
  map_zero' := MonoidAlgebra.comapDomain_zero _ _
  map_add' x y := MonoidAlgebra.comapDomain_add _ _ x y

theorem pi_apply (hι : Function.Injective ι) (t : G) (x : MonoidAlgebra k G) (h : H) :
    (pi ι hι t x).coeff h = x.coeff (cMap ι t h) := by
  show (MonoidAlgebra.comapDomain (cMap ι t) (cMap_injective ι hι t) x).coeff h =
    x.coeff (cMap ι t h)
  rw [MonoidAlgebra.coeff_comapDomain]
  exact Finsupp.comapDomain_apply (cMap ι t) x.coeff ((cMap_injective ι hι t).injOn) h

theorem pi_iota (hι : Function.Injective ι) (t : G) (z : MonoidAlgebra k H) :
    pi ι hι t (iota ι t z) = z := by
  apply MonoidAlgebra.ext
  ext h
  rw [pi_apply ι hι, iota_apply_self ι hι]

/-- On a different coset, `iota s z` vanishes. -/
theorem iota_apply_eq_zero (_hι : Function.Injective ι) {s t : G}
    (hst : (QuotientGroup.mk s : G ⧸ ι.range) ≠ QuotientGroup.mk t)
    (z : MonoidAlgebra k H) (h : H) :
    (iota ι s z).coeff (cMap ι t h) = 0 := by
  classical
  simp only [iota_apply_eq]
  rw [← Finsupp.notMem_support_iff]
  intro hmem
  refine hst ?_
  have h2 := Finsupp.mapDomain_support (s := z.coeff) (f := cMap ι s) hmem
  rw [Finset.mem_image] at h2
  obtain ⟨h', _, hh'⟩ := h2
  rw [← mk_cMap ι s h', hh', mk_cMap ι t h]

/-- Every `g` lies in the coset of its own representative. -/
theorem exists_eq_cMap_out (g : G) :
    ∃ h : H, g = cMap ι (QuotientGroup.mk g : G ⧸ ι.range).out h := by
  have hmem : ((Quotient.out (QuotientGroup.mk g : G ⧸ ι.range))⁻¹ * g) ∈ ι.range := by
    rw [← QuotientGroup.eq]
    exact QuotientGroup.out_eq' _
  obtain ⟨h, hh⟩ := hmem
  exact ⟨h, by rw [cMap, hh, mul_inv_cancel_left]⟩

/-- Decomposition of an element of `k[G]` into its coset components. -/
theorem eq_sum_iota_pi (hι : Function.Injective ι) (x : MonoidAlgebra k G)
    (T : Finset (G ⧸ ι.range)) (hT : ∀ g ∈ x.coeff.support, QuotientGroup.mk g ∈ T) :
    x = ∑ c ∈ T, iota ι c.out (pi ι hι c.out x) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  obtain ⟨h0, h0eq⟩ := exists_eq_cMap_out ι g
  set t : G ⧸ ι.range := QuotientGroup.mk g with ht
  have hg : g = cMap ι t.out h0 := h0eq
  have hsum : (∑ c ∈ T, iota ι c.out (pi ι hι c.out x)).coeff g
      = ∑ c ∈ T, (iota ι c.out (pi ι hι c.out x)).coeff g := by simp
  rw [hsum]
  by_cases hgc : t ∈ T
  · rw [Finset.sum_eq_single t]
    · rw [hg]
      exact ((iota_apply_self ι hι t.out (pi ι hι t.out x) h0).trans
        (pi_apply ι hι t.out x h0)).symm
    · intro c hc hne
      rw [hg]
      refine iota_apply_eq_zero ι hι ?_ (pi ι hι c.out x) h0
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq']
      exact hne
    · intro h; exact absurd hgc h
  · rw [Finset.sum_eq_zero]
    · rw [← Finsupp.notMem_support_iff]
      intro hmem
      exact hgc (by rw [ht]; exact hT g hmem)
    · intro c hc
      rw [hg]
      refine iota_apply_eq_zero ι hι ?_ (pi ι hι c.out x) h0
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq']
      exact fun h => hgc (h ▸ hc)

end Coset

/-! ## Naturality of the generator vectors -/

section Naturality

variable {k : Type*} [CommRing k]

variable {d : ℕ} {G H : Type*} [Group G] [Group H]

/-- The generator vector of `ι ∘ f` is the image of that of `f` under `mapDomainAlgHom`. -/
theorem gGenSubOne_comp (ι : H →* G) (f : FreeGroup (Fin d) →* H) (i : Fin d) :
    gGenSubOne k (ι.comp f) i =
      MonoidAlgebra.mapDomainAlgHom k k ι (gGenSubOne k f i) := by
  rw [gGenSubOne, gGenSubOne, groupAlgMap_comp, AlgHom.comp_apply, map_sub, map_one]

/-- `mapDomain (cMap ι t)` is multiplication by `of t` composed with `mapDomainAlgHom`. -/
theorem mapDomain_cMap_eq (ι : H →* G) (t : G) (z : MonoidAlgebra k H) :
    MonoidAlgebra.mapDomain (cMap ι t) z =
      MonoidAlgebra.of k G t * MonoidAlgebra.mapDomainAlgHom k k ι z := by
  induction z using MonoidAlgebra.induction_on with
  | of h =>
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.of_apply,
      MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.single_mul_single, mul_one]
  | add a b iha ihb =>
    show MonoidAlgebra.mapDomain (cMap ι t) (a + b) = _
    rw [MonoidAlgebra.mapDomain_add, iha, ihb, map_add, mul_add]
  | smul r a iha =>
    show MonoidAlgebra.mapDomain (cMap ι t) (r • a) = _
    rw [MonoidAlgebra.mapDomain_smul, iha]
    simp only [MonoidAlgebra.mapDomainAlgHom_apply]
    simp only [MonoidAlgebra.mapDomain_smul]
    simp only [mul_smul_comm]

theorem iota_eq_of_mul (ι : H →* G) (t : G) (z : MonoidAlgebra k H) :
    iota ι t z = MonoidAlgebra.of k G t * MonoidAlgebra.mapDomainAlgHom k k ι z := by
  rw [iota_apply_eq]
  exact mapDomain_cMap_eq ι t z

/-- `iota t` is compatible with the multiplication of `k[H]` and the algebra map. -/
theorem iota_mul_mapDomainAlgHom (ι : H →* G) (t : G) (a b : MonoidAlgebra k H) :
    iota ι t a * MonoidAlgebra.mapDomainAlgHom k k ι b = iota ι t (a * b) := by
  rw [iota_eq_of_mul, iota_eq_of_mul, mul_assoc, ← map_mul]

end Naturality

/-! ## Expansion of `ψ_{ι ∘ f}` along cosets -/

section Expand

variable {k : Type*} [CommRing k]

variable {d : ℕ} {G H : Type*} [Group G] [Group H]

theorem psi_comp_expand (ι : H →* G) (hι : Function.Injective ι)
    (f : FreeGroup (Fin d) →* H) (x : Fin d → MonoidAlgebra k G)
    (T : Finset (G ⧸ ι.range))
    (hT : ∀ i, ∀ g ∈ (x i).coeff.support, QuotientGroup.mk g ∈ T) :
    psi k (ι.comp f) x =
      ∑ c ∈ T, iota ι c.out (psi k f (fun i => pi ι hι c.out (x i))) := by
  have hdecomp : ∀ i, x i = ∑ c ∈ T, iota ι c.out (pi ι hι c.out (x i)) :=
    fun i => eq_sum_iota_pi ι hι (x i) T (hT i)
  calc
    psi k (ι.comp f) x
        = ∑ i, x i * gGenSubOne k (ι.comp f) i := psi_apply k (ι.comp f) x
    _ = ∑ i, x i * MonoidAlgebra.mapDomainAlgHom k k ι (gGenSubOne k f i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [gGenSubOne_comp]
    _ = ∑ i, (∑ c ∈ T, iota ι c.out (pi ι hι c.out (x i))) *
            MonoidAlgebra.mapDomainAlgHom k k ι (gGenSubOne k f i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          conv_lhs => rw [hdecomp i]
    _ = ∑ i, ∑ c ∈ T, iota ι c.out (pi ι hι c.out (x i)) *
            MonoidAlgebra.mapDomainAlgHom k k ι (gGenSubOne k f i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ c ∈ T, iota ι c.out (pi ι hι c.out (x i) * gGenSubOne k f i) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => ?_))
          rw [iota_mul_mapDomainAlgHom]
    _ = ∑ c ∈ T, ∑ i, iota ι c.out (pi ι hι c.out (x i) * gGenSubOne k f i) :=
          Finset.sum_comm
    _ = ∑ c ∈ T, iota ι c.out (∑ i, pi ι hι c.out (x i) * gGenSubOne k f i) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [map_sum]
    _ = ∑ c ∈ T, iota ι c.out (psi k f (fun i => pi ι hι c.out (x i))) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [psi_apply]

end Expand

/-! ## Pushing a span forward along `mapDomainAlgHom` -/

section Push

variable {k : Type*} [CommRing k]

variable {d r : ℕ} {G H : Type*} [Group G] [Group H]

theorem mapDomainAlgHom_mem_span (ι : H →* G) (f : FreeGroup (Fin d) →* H)
    (R : Fin r → FreeGroup (Fin d)) (z : Fin d → MonoidAlgebra k H)
    (hz : z ∈ Submodule.span (MonoidAlgebra k H) (Set.range (fun j => Vfun k f (R j)))) :
    (fun i => MonoidAlgebra.mapDomainAlgHom k k ι (z i)) ∈
      Submodule.span (MonoidAlgebra k G) (Set.range (fun j => Vfun k (ι.comp f) (R j))) := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    rw [← Vfun_comp (k := k) (ι := ι) (f := f) (w := R j)]
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero =>
    have h0 : (fun i => MonoidAlgebra.mapDomainAlgHom k k ι
        ((0 : Fin d → MonoidAlgebra k H) i)) = 0 := by
      ext i; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
    have h : (fun i => MonoidAlgebra.mapDomainAlgHom k k ι ((a + b) i)) =
        (fun i => MonoidAlgebra.mapDomainAlgHom k k ι (a i)) +
          (fun i => MonoidAlgebra.mapDomainAlgHom k k ι (b i)) := by
      funext i
      simp only [Pi.add_apply, map_add]
    rw [h]
    exact Submodule.add_mem _ iha ihb
  | smul c a _ iha =>
    have h : (fun i => MonoidAlgebra.mapDomainAlgHom k k ι ((c • a) i)) =
        MonoidAlgebra.mapDomainAlgHom k k ι c •
          (fun i => MonoidAlgebra.mapDomainAlgHom k k ι (a i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [h]
    exact Submodule.smul_mem _ _ iha

end Push

/-! ## The descent theorem -/

theorem ker_psi_le_span_comp {k : Type*} [CommRing k] {d r : ℕ} {G H : Type*} [Group G] [Group H]
    (ι : H →* G) (hι : Function.Injective ι) (f : FreeGroup (Fin d) →* H)
    (R : Fin r → FreeGroup (Fin d))
    (h : LinearMap.ker (Work.GolodShafarevich.psi k f) ≤
      Submodule.span (MonoidAlgebra k H)
        (Set.range (fun j => Work.GolodShafarevich.Vfun k f (R j)))) :
    LinearMap.ker (Work.GolodShafarevich.psi k (ι.comp f)) ≤
      Submodule.span (MonoidAlgebra k G)
        (Set.range (fun j => Work.GolodShafarevich.Vfun k (ι.comp f) (R j))) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  classical
  set T : Finset (G ⧸ ι.range) :=
    (Finset.univ : Finset (Fin d)).biUnion
      (fun i => (x i).coeff.support.image (fun g => (QuotientGroup.mk g : G ⧸ ι.range)))
    with hTdef
  have hTmem : ∀ i : Fin d, ∀ g ∈ (x i).coeff.support,
      (QuotientGroup.mk g : G ⧸ ι.range) ∈ T := by
    intro i g hg
    rw [hTdef]
    exact Finset.subset_biUnion_of_mem
      (fun i : Fin d => (x i).coeff.support.image (fun g => (QuotientGroup.mk g : G ⧸ ι.range)))
      (Finset.mem_univ i) (Finset.mem_image_of_mem _ hg)
  have hpsi : psi k (ι.comp f) x =
      ∑ c ∈ T, iota ι c.out (psi k f (fun i => pi ι hι c.out (x i))) :=
    psi_comp_expand ι hι f x T hTmem
  have hzero : ∀ c ∈ T, psi k f (fun i => pi ι hι c.out (x i)) = 0 := by
    intro c hc
    apply MonoidAlgebra.ext
    ext h
    show (psi k f (fun i => pi ι hι c.out (x i))).coeff h = 0
    have h2 : (∑ c' ∈ T, iota ι c'.out (psi k f (fun i => pi ι hι c'.out (x i)))).coeff
        (cMap ι c.out h) = 0 := by
      rw [← hpsi, hx]
      simp
    have hsum : (∑ c' ∈ T, iota ι c'.out (psi k f (fun i => pi ι hι c'.out (x i)))).coeff
          (cMap ι c.out h)
        = (psi k f (fun i => pi ι hι c.out (x i))).coeff h := by
      rw [show (∑ c' ∈ T, iota ι c'.out (psi k f (fun i => pi ι hι c'.out (x i)))).coeff
            (cMap ι c.out h)
          = ∑ c' ∈ T, (iota ι c'.out (psi k f (fun i => pi ι hι c'.out (x i)))).coeff
              (cMap ι c.out h) from by simp]
      rw [Finset.sum_eq_single c]
      · rw [iota_apply_self ι hι]
      · intro c' hc' hne
        exact iota_apply_eq_zero ι hι (by
          rw [QuotientGroup.out_eq', QuotientGroup.out_eq']; exact hne) _ h
      · intro hc'; exact absurd hc hc'
    rw [← hsum]
    exact h2
  have hspan : ∀ c ∈ T, (fun i => pi ι hι c.out (x i)) ∈
      Submodule.span (MonoidAlgebra k H) (Set.range (fun j => Vfun k f (R j))) :=
    fun c hc => h (LinearMap.mem_ker.mpr (hzero c hc))
  have hpush : ∀ c ∈ T, (fun i => iota ι c.out (pi ι hι c.out (x i))) ∈
      Submodule.span (MonoidAlgebra k G)
        (Set.range (fun j => Vfun k (ι.comp f) (R j))) := by
    intro c hc
    have hmap := mapDomainAlgHom_mem_span ι f R (fun i => pi ι hι c.out (x i)) (hspan c hc)
    have heq : (fun i => iota ι c.out (pi ι hι c.out (x i))) =
        MonoidAlgebra.of k G c.out •
          (fun i => MonoidAlgebra.mapDomainAlgHom k k ι (pi ι hι c.out (x i))) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact iota_eq_of_mul ι c.out (pi ι hι c.out (x i))
    rw [heq]
    exact Submodule.smul_mem _ _ hmap
  have hxsum : x = ∑ c ∈ T, (fun i => iota ι c.out (pi ι hι c.out (x i))) := by
    funext i
    rw [Finset.sum_apply]
    exact eq_sum_iota_pi ι hι (x i) T (hTmem i)
  rw [hxsum]
  exact Submodule.sum_mem _ hpush

end Work.GolodShafarevich.RelationModule
