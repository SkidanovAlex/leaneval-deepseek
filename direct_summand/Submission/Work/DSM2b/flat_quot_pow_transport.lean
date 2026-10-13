import Mathlib

namespace Work.DSM2b

universe u

/-- **Transport of flatness along a ring isomorphism and a compatible additive equivalence.**
If `f : M ≃+ N` intertwines the scalar actions through a ring isomorphism `e : R ≃+* S`,
and `M` is flat over `R`, then `N` is flat over `S`.

Proof: the equational criterion for flatness `Module.Flat.iff_forall_isTrivialRelation`. A
relation `∑ gᵢ • yᵢ = 0` in `N` is pulled back by `e.symm`/`f.symm` to a relation in `M`, a
trivialisation of which is pushed forward by `e`/`f`. -/
theorem flat_congr_aux {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : R ≃+* S) (f : M ≃+ N) (hf : ∀ (r : R) (m : M), f (r • m) = e r • f m)
    (h : Module.Flat R M) : Module.Flat S N := by
  rw [Module.Flat.iff_forall_isTrivialRelation] at h ⊢
  intro l g y hgy
  have hsum : ∑ i, (e.symm (g i)) • (f.symm (y i)) = 0 := by
    apply f.injective
    rw [map_zero, map_sum]
    rw [Finset.sum_congr rfl (fun i _ => hf (e.symm (g i)) (f.symm (y i)))]
    simpa using hgy
  obtain ⟨k, a, z, hza, haz⟩ :=
    h (f := fun i => e.symm (g i)) (x := fun i => f.symm (y i)) hsum
  have hza' : ∀ i, f.symm (y i) = ∑ j, a i j • z j := fun i => hza i
  have haz' : ∀ j, ∑ i, e.symm (g i) * a i j = 0 := fun j => haz j
  refine ⟨k, (fun i j => e (a i j)), (fun j => f (z j)), ?_, ?_⟩
  · intro i
    have h1 : y i = ∑ j, e (a i j) • f (z j) := by
      calc y i = f (f.symm (y i)) := (f.apply_symm_apply (y i)).symm
        _ = f (∑ j, a i j • z j) := by rw [hza' i]
        _ = ∑ j, f (a i j • z j) := by rw [map_sum]
        _ = ∑ j, e (a i j) • f (z j) := Finset.sum_congr rfl (fun j _ => hf (a i j) (z j))
    exact h1
  · intro j
    have h2 : (∑ i, g i * e (a i j)) = 0 := by
      have h3 : e (∑ i, e.symm (g i) * a i j) = 0 := by rw [haz' j, map_zero]
      rw [map_sum] at h3
      rw [← h3]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      simp
    exact h2

/-- **The two descriptions of the kernel of the double quotient agree.** For ideals `I, J ⊆ R`
and an `R`-algebra `B`, the image of `I · B` in `B ⧸ J · B` equals the submodule generated over
`R ⧸ J` by (the image of) `I`. This is the structural fact behind the Third Isomorphism Theorem
for the pair `(B ⧸ J·B) ⧸ I·(B ⧸ J·B) ≅ B ⧸ I·B`. -/
lemma map_mkQ_eq_smul_top {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I J : Ideal R) :
    ((Submodule.map (Submodule.mkQ (J.map (algebraMap R B))) (I.map (algebraMap R B)) :
        Submodule B (B ⧸ J.map (algebraMap R B))) : Set (B ⧸ J.map (algebraMap R B)))
      = (((I.map (Ideal.Quotient.mk J)) •
          (⊤ : Submodule (R ⧸ J) (B ⧸ J.map (algebraMap R B))) :
            Submodule (R ⧸ J) (B ⧸ J.map (algebraMap R B))) :
          Set (B ⧸ J.map (algebraMap R B))) := by
  rw [Ideal.smul_top_eq_map, Submodule.coe_restrictScalars]
  rw [Ideal.map_map]
  rw [show (algebraMap (R ⧸ J) (B ⧸ J.map (algebraMap R B))).comp (Ideal.Quotient.mk J)
      = (Ideal.Quotient.mk (J.map (algebraMap R B))).comp (algebraMap R B)
      from RingHom.ext (fun x => rfl)]
  rw [← Ideal.map_map]
  rw [Ideal.map_eq_submodule_map (Ideal.Quotient.mk (J.map (algebraMap R B)))]
  rfl

/-- The action of `R ⧸ I` on `B ⧸ I·B` on representatives. -/
lemma quot_smul_mk {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (r : R) (b : B) :
    (Ideal.Quotient.mk I r) •
        (Ideal.Quotient.mk (I.map (algebraMap R B)) b : B ⧸ I.map (algebraMap R B))
      = Ideal.Quotient.mk (I.map (algebraMap R B)) (r • b) := by
  rw [Algebra.smul_def]
  rw [show (algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B)) (Ideal.Quotient.mk I r))
      = Ideal.Quotient.mk (I.map (algebraMap R B)) (algebraMap R B r) from rfl]
  rw [← map_mul, Algebra.smul_def]

/-- **Flatness of the double quotient, general form.** Let `J ≤ I` be ideals of `R`, `B` an
`R`-algebra. If `B ⧸ I·B` is flat over `R ⧸ I`, then `(B ⧸ J·B) ⧸ I·(B ⧸ J·B)` is flat over
`(R ⧸ J) ⧸ I`. The two modules are identified through the Third Isomorphism Theorem
(`DoubleQuot.quotQuotEquivQuotOfLE` and `Submodule.quotientQuotientEquivQuotient`). -/
theorem flat_quot_quot_of_le {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I J : Ideal R) (hJI : J ≤ I)
    (h : Module.Flat (R ⧸ I) (B ⧸ I.map (algebraMap R B))) :
    Module.Flat ((R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J))
      ((B ⧸ J.map (algebraMap R B)) ⧸ (I.map (Ideal.Quotient.mk J)) • (⊤ : Submodule
        (R ⧸ J) (B ⧸ J.map (algebraMap R B)))) := by
  classical
  let p : Ideal B := I.map (algebraMap R B)
  let q : Ideal B := J.map (algebraMap R B)
  let K : Ideal (R ⧸ J) := I.map (Ideal.Quotient.mk J)
  let WB : Submodule B (B ⧸ q) := Submodule.map (Submodule.mkQ q) p
  let W : Submodule (R ⧸ J) (B ⧸ q) := K • ⊤
  have hpq : q ≤ p := Ideal.map_mono hJI
  -- the two submodules have the same carrier
  have hc : (WB : Set (B ⧸ q)) = (W : Set (B ⧸ q)) := map_mkQ_eq_smul_top I J
  have hsub : WB.toAddSubgroup = W.toAddSubgroup := by
    apply SetLike.ext
    intro x
    exact Set.ext_iff.mp hc x
  -- the ring isomorphism
  let he : (R ⧸ I) ≃+* ((R ⧸ J) ⧸ K) := (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm
  have he_apply : ∀ r : R, he (Ideal.Quotient.mk I r)
      = Ideal.Quotient.mk K (Ideal.Quotient.mk J r) := by
    intro r
    change (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm (Ideal.Quotient.mk I r)
      = Ideal.Quotient.mk K (Ideal.Quotient.mk J r)
    rw [DoubleQuot.quotQuotEquivQuotOfLE_symm_mk r hJI]
    rfl
  -- the two quotient maps
  have hkerα : p ≤ (WB.mkQ ∘ₗ Submodule.mkQ q).ker := by
    intro x hx
    change WB.mkQ (Submodule.mkQ q x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_map_of_mem hx
  have hq_ker : q ≤ p.mkQ.ker := by rw [Submodule.ker_mkQ]; exact hpq
  have hkerβ : WB ≤ (Submodule.liftQ q p.mkQ hq_ker).ker := by
    intro z hz
    rw [Submodule.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    change (Submodule.liftQ q p.mkQ hq_ker) (Submodule.mkQ q x) = 0
    rw [Submodule.mkQ_apply]
    rw [Submodule.liftQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  let α : (B ⧸ p) →ₗ[B] (B ⧸ q) ⧸ WB :=
    Submodule.liftQ p (WB.mkQ ∘ₗ Submodule.mkQ q) hkerα
  let β : ((B ⧸ q) ⧸ WB) →ₗ[B] (B ⧸ p) :=
    Submodule.liftQ WB (Submodule.liftQ q p.mkQ hq_ker) hkerβ
  have α_apply : ∀ b : B, α (Submodule.Quotient.mk (p := p) b)
      = Submodule.Quotient.mk (p := WB) (Submodule.Quotient.mk (p := q) b) := by
    intro b
    rw [show α = Submodule.liftQ p (WB.mkQ ∘ₗ Submodule.mkQ q) hkerα from rfl]
    rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  have β_apply : ∀ z : B ⧸ q, β (Submodule.Quotient.mk (p := WB) z)
      = (Submodule.liftQ q p.mkQ hq_ker) z := by
    intro z
    rw [show β = Submodule.liftQ WB (Submodule.liftQ q p.mkQ hq_ker) hkerβ from rfl]
    rw [Submodule.liftQ_apply]
  have hαβ : ∀ x, β (α x) = x := by
    intro x
    refine Submodule.Quotient.induction_on p x (fun b => ?_)
    rw [α_apply b, β_apply (Submodule.Quotient.mk (p := q) b)]
    rw [Submodule.liftQ_apply, Submodule.mkQ_apply]
  have hβα : ∀ y, α (β y) = y := by
    intro y
    refine Submodule.Quotient.induction_on WB y (fun z => ?_)
    rw [β_apply z]
    refine Submodule.Quotient.induction_on q z (fun b => ?_)
    rw [Submodule.liftQ_apply, Submodule.mkQ_apply, α_apply b]
  let f₀ : (B ⧸ p) ≃+ ((B ⧸ q) ⧸ WB) :=
    { toFun := α, invFun := β, left_inv := hαβ, right_inv := hβα, map_add' := α.map_add }
  let bridge : ((B ⧸ q) ⧸ WB) ≃+ ((B ⧸ q) ⧸ W) :=
    QuotientAddGroup.quotientAddEquivOfEq hsub
  let f : (B ⧸ p) ≃+ ((B ⧸ q) ⧸ W) := f₀.trans bridge
  have f_apply : ∀ b : B, f (Submodule.Quotient.mk (p := p) b)
      = Submodule.Quotient.mk (p := W) (Submodule.Quotient.mk (p := q) b) := by
    intro b
    change bridge (f₀ (Submodule.Quotient.mk (p := p) b)) = _
    rw [show f₀ (Submodule.Quotient.mk (p := p) b)
        = Submodule.Quotient.mk (p := WB) (Submodule.Quotient.mk (p := q) b)
        from α_apply b]
    exact QuotientAddGroup.quotientAddEquivOfEq_mk hsub (Submodule.Quotient.mk (p := q) b)
  refine flat_congr_aux he f ?_ h
  intro a m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine Submodule.Quotient.induction_on p m (fun b => ?_)
  have hsm : (Ideal.Quotient.mk I r) • (Submodule.Quotient.mk (p := p) b)
      = Submodule.Quotient.mk (p := p) (r • b) := quot_smul_mk I r b
  have hsm2 : (Ideal.Quotient.mk J r) • (Submodule.Quotient.mk (p := q) b)
      = Submodule.Quotient.mk (p := q) (r • b) := quot_smul_mk J r b
  rw [hsm, f_apply (r • b), f_apply b, he_apply r]
  rw [show (Ideal.Quotient.mk K (Ideal.Quotient.mk J r)) •
        (Submodule.Quotient.mk (p := W) (Submodule.Quotient.mk (p := q) b))
      = Submodule.Quotient.mk (p := W)
        ((Ideal.Quotient.mk J r) • (Submodule.Quotient.mk (p := q) b))
      from Module.Quotient.mk_smul_mk (B ⧸ q) K (Ideal.Quotient.mk J r)
        (Submodule.Quotient.mk (p := q) b)]
  rw [hsm2]

/-- Transport of flatness across the canonical identifications
`(R ⧸ π^{n+1}) ⧸ (π^n) ≅ R ⧸ π^n` (Third Isomorphism Theorem, `Ideal.quotQuotEquivQuotOfLE`
with `I = span{π^{n+1}} ≤ J = span{π^n}`)
and `(B ⧸ π^{n+1}B) ⧸ (π^n ·) ≅ B ⧸ π^nB` (`Submodule.quotientQuotientEquivQuotient`).

If `B ⧸ π^n B` is flat over `R ⧸ π^n` then `(B ⧸ π^{n+1}B) ⧸ (π^n ·)` is flat over
`(R ⧸ π^{n+1}) ⧸ (π^n)`.

One way: exhibit `e : (R ⧸ π^{n+1}) ⧸ (π^n) ≃+* R ⧸ π^n` (via `Ideal.quotQuotEquivQuotOfLE`
with `I = Ideal.span {π ^ (n+1)}`, `J = Ideal.span {π ^ n}`)
and `f : ((B ⧸ π^{n+1}B) ⧸ π^n·) ≃+ (B ⧸ π^nB)` (via `Submodule.quotientQuotientEquivQuotient`,
after identifying the submodule `(π^n) • ⊤` of `B ⧸ π^{n+1}B` with `(π^n B).map (π^{n+1}B).mkQ`),
together with `∀ a m, f (a • m) = e a • f m`, and conclude with the general transport lemma
`Work.DSM2b.flat_congr` (import `Submission.Work.DSM2b.flat_congr`, available at path
`DSM2b/flat_congr`); the compatibility is provable by quotient induction since both maps are
induced by the identity on `R` and on `B`. -/
theorem flat_quot_pow_transport {R B : Type u} [CommRing R] (π : R) [CommRing B] [Algebra R B]
    (n : ℕ)
    (h : Module.Flat (R ⧸ Ideal.span {π ^ n}) (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B))) :
    Module.Flat
      ((R ⧸ Ideal.span {π ^ (n + 1)}) ⧸
        (Ideal.span {π ^ n}).map (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})))
      ((B ⧸ (Ideal.span {π ^ (n + 1)}).map (algebraMap R B)) ⧸
        ((Ideal.span {π ^ n}).map (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}))) • (⊤ : Submodule
          (R ⧸ Ideal.span {π ^ (n + 1)})
          (B ⧸ (Ideal.span {π ^ (n + 1)}).map (algebraMap R B)))) := by
  have hJI : Ideal.span {π ^ (n + 1)} ≤ Ideal.span {π ^ n} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨π, pow_succ π n⟩
  exact flat_quot_quot_of_le (Ideal.span {π ^ n}) (Ideal.span {π ^ (n + 1)}) hJI h

end Work.DSM2b
