import Mathlib
import Submission.Work.BW.rank_one_cut_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped Pointwise

/-- **The `P`-torsion kernel of `M ⧸ N` is `(N ∩ P·M)/P·N`.**
With `cutQ P N = N ∩ P·M` (a submodule of `N`), `cutPNQ P N = P·N` (a submodule of `cutQ P N`) and
`cutMap P N = P·` acting on `M ⧸ N`, the length of `cutQ P N ⧸ cutPNQ P N` equals the length of the
kernel of `cutMap P N`. Route: `K := (lsmul P).comap N` satisfies `K.map (lsmul P) = cutQ P N`
(`Submodule.map_comap_eq`, `cutPM_eq_range`), and `x ↦ P • x` is a linear isomorphism `K ≃ₗ cutQ P N`
by `hP` for injectivity and `LinearMap.mem_range` for surjectivity; it carries
`N.submoduleOf K` onto `cutPNQ P N`, so `Submodule.Quotient.equiv` gives
`K ⧸ (N.submoduleOf K) ≃ₗ cutQ P N ⧸ cutPNQ P N`. On the other hand `cutMap_ker` identifies
`(cutMap P N).ker = K.map N.mkQ`, and `N.mkQ ∘ K.subtype : K →ₗ M ⧸ N` has kernel `N.submoduleOf K`
and range `K.map N.mkQ`, so `LinearMap.quotKerEquivRange` gives `K ⧸ (N.submoduleOf K) ≃ₗ (cutMap P N).ker`. -/
theorem cut_torsion_length {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (P : A) (N : Submodule A M) (hP : ∀ y : M, P • y = 0 → y = 0) :
    Module.length A (cutQ P N ⧸ cutPNQ P N) = Module.length A (cutMap P N).ker := by
  -- `P·N`, computed inside `N`, is the range of `P·` acting on `N`.
  have hcutPN : cutPN P N = (LinearMap.lsmul A N P).range := by
    rw [cutPN, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
      Submodule.map_top]
    rfl
  -- `K = {x : M | P • x ∈ N}`
  let K : Submodule A M := Submodule.comap (LinearMap.lsmul A M P) N
  -- `P·` as a map `K → cutQ P N`
  let φ : K →ₗ[A] cutQ P N :=
    { toFun := fun x => ⟨⟨P • (x : M), x.2⟩, by
        rw [cutQ, Submodule.mem_comap]
        show P • (x : M) ∈ cutPM (M := M) P
        rw [cutPM_eq_range]
        exact LinearMap.mem_range_self _ (x : M)⟩
      map_add' := fun x y => by
        apply Subtype.ext; apply Subtype.ext; exact smul_add P (x : M) (y : M)
      map_smul' := fun a x => by
        apply Subtype.ext; apply Subtype.ext; exact (smul_comm a P (x : M)).symm }
  have he : ∀ x : K, ((φ x : cutQ P N) : M) = P • (x : M) := fun _ => rfl
  -- `P·` is injective on `M` by hypothesis, and surjective onto `N ∩ P·M` by construction
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : P • (x : M) = P • (y : M) := congrArg (fun z : cutQ P N => ((z : N) : M)) hxy
      have h3 : P • ((x : M) - (y : M)) = 0 := by rw [smul_sub, h1, sub_self]
      exact Subtype.ext (sub_eq_zero.mp (hP _ h3))
    · intro n
      obtain ⟨y, hy⟩ : ∃ y : M, P • y = ((n : N) : M) := by
        have hn : ((n : N) : M) ∈ cutPM (M := M) P := n.2
        rw [cutPM_eq_range, LinearMap.mem_range] at hn
        obtain ⟨y, hy⟩ := hn
        exact ⟨y, hy⟩
      refine ⟨⟨y, ?_⟩, ?_⟩
      · show (LinearMap.lsmul A M P) y ∈ N
        rw [LinearMap.lsmul_apply, hy]; exact (n : N).2
      · apply Subtype.ext; apply Subtype.ext; exact hy
  let e : K ≃ₗ[A] cutQ P N := LinearEquiv.ofBijective φ hφ
  -- `P·` carries `N ∩ K` onto `P·N` (inside `N ∩ P·M`)
  have hmap : Submodule.map (φ : K →ₗ[A] cutQ P N) (N.submoduleOf K) = cutPNQ P N := by
    apply le_antisymm
    · rintro q ⟨x, hx, rfl⟩
      rw [cutPNQ, Submodule.mem_comap, hcutPN, LinearMap.mem_range]
      refine ⟨⟨(x : M), hx⟩, ?_⟩
      apply Subtype.ext
      exact (he x).symm
    · intro q hq
      rw [cutPNQ, Submodule.mem_comap, hcutPN, LinearMap.mem_range] at hq
      obtain ⟨w, hw⟩ := hq
      have hw'' : P • (w : M) = ((q : cutQ P N) : M) := by
        simpa using congrArg (fun z : N => (z : M)) hw
      have hq2 : ((q : cutQ P N) : M) ∈ cutPM (M := M) P := (q : cutQ P N).2
      rw [cutPM_eq_range, LinearMap.mem_range] at hq2
      obtain ⟨y, hy⟩ := hq2
      have hy' : P • y = ((q : cutQ P N) : M) := hy
      have hyw : y = w := by
        have hz : P • (y - (w : M)) = 0 := by rw [smul_sub, hy', hw'', sub_self]
        exact sub_eq_zero.mp (hP _ hz)
      rw [Submodule.mem_map]
      refine ⟨⟨y, ?_⟩, ?_, ?_⟩
      · show (LinearMap.lsmul A M P) y ∈ N
        rw [LinearMap.lsmul_apply, hy']; exact q.1.2
      · show (y : M) ∈ N
        rw [hyw]; exact (w : N).2
      · apply Subtype.ext; apply Subtype.ext
        exact (he ⟨y, _⟩).trans hy'
  let e1 : (K ⧸ N.submoduleOf K) ≃ₗ[A] (cutQ P N ⧸ cutPNQ P N) :=
    Submodule.Quotient.equiv (N.submoduleOf K) (cutPNQ P N) e hmap
  -- the projection `K → M ⧸ N`
  let g : K →ₗ[A] M ⧸ N := N.mkQ.comp K.subtype
  have hker : g.ker = N.submoduleOf K := by
    show (N.mkQ.comp K.subtype).ker = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rfl
  have hrange : g.range = (cutMap P N).ker := by
    rw [cutMap_ker]
    show (N.mkQ.comp K.subtype).range = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e2 : (K ⧸ N.submoduleOf K) ≃ₗ[A] (cutMap P N).ker := by
    have h := LinearMap.quotKerEquivRange g
    rw [hker, hrange] at h
    exact h
  rw [← LinearEquiv.length_eq e1, LinearEquiv.length_eq e2]

end Work.BW
