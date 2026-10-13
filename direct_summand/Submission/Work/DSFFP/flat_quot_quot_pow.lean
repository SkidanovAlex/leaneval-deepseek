import Mathlib
import Submission.Work.DSFFP.Defs

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.DSFFP

/-- A module that is a subsingleton is flat: any relation `∑ fᵢ • xᵢ = 0` is trivial since all its
terms vanish. -/
lemma flat_of_subsingleton {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Subsingleton M] : Module.Flat R M := by
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x _
  exact ⟨0, fun i j => 0, fun j => (0 : M), fun i => Subsingleton.elim _ _, fun j => by simp⟩

/-- Flatness transports across a ring equivalence together with a compatible additive equivalence of
the modules: if `e : R ≃+* S` and `f : M ≃+ N` intertwine the scalar actions, then a flat `R`-module
`M` gives a flat `S`-module `N`.

This is the equational criterion (`Module.Flat.iff_forall_isTrivialRelation`) transported along `e`
and `f`: a relation in `N` is pulled back to a relation in `M`, trivialised there, and pushed
forward again. -/
theorem flat_congr {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = e r • f m) (h : Module.Flat R M) : Module.Flat S N := by
  rw [Module.Flat.iff_forall_isTrivialRelation] at h ⊢
  intro l g y hy
  have hrel : ∑ i, (e.symm (g i)) • (f.symm (y i)) = (0 : M) := by
    apply f.injective
    rw [map_zero, map_sum]
    simp only [hf, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    simpa using hy
  obtain ⟨k, a', z', h1, h2⟩ := h hrel
  refine ⟨k, fun i j => e (a' i j), fun j => f (z' j), ?_, ?_⟩
  · intro i
    have := congrArg f (h1 i)
    simp only [map_sum, hf] at this
    simpa using this
  · intro j
    have := congrArg e (h2 j)
    simp only [map_sum, map_mul, map_zero] at this
    simpa using this

/-- The engine behind `flat_quot_quot_pow`.  Let `A → B` be a map of commutative rings, `I ≤ (j)` an
inclusion of ideals and suppose `B ⧸ jB` is flat over `A ⧸ (j)`.  Then the "double quotient"
`(B ⧸ IB) ⧸ (j̄)·⊤` is flat over `(A ⧸ I) ⧸ (j̄)`.

Both the ring `(A ⧸ I) ⧸ (j̄)` and the module `(B ⧸ IB) ⧸ (j̄)·⊤` are third-isomorphism-theorem
quotients of `A ⧸ (j)` and `B ⧸ jB`; the two identifications are built from
`DoubleQuot.quotQuotEquivQuotOfLE`, `Ideal.quotEquivOfEq`, `Submodule.quotEquivOfEq` and
`Ideal.smul_top_eq_map`, are compatible with the scalar actions, and `flat_congr` transports
flatness across them. -/
theorem flat_quot_quot_span {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (j : A) (hle : I ≤ Ideal.span {j})
    (h : Module.Flat (A ⧸ Ideal.span {j}) (B ⧸ (Ideal.span {j}).map (algebraMap A B))) :
    Module.Flat ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I j})
      ((B ⧸ I.map (algebraMap A B)) ⧸
        (Ideal.span {Ideal.Quotient.mk I j}) • (⊤ : Submodule (A ⧸ I) (B ⧸ I.map (algebraMap A B)))) := by
  let M : Ideal B := I.map (algebraMap A B)
  let N : Ideal B := (Ideal.span {j}).map (algebraMap A B)
  let K : Ideal (A ⧸ I) := Ideal.span {Ideal.Quotient.mk I j}
  have hN : N = Ideal.span {algebraMap A B j} := by
    dsimp only [N]; rw [Ideal.map_span, Set.image_singleton]
  have hleM : M ≤ N := Ideal.map_mono hle
  have hK : K = (Ideal.span {j}).map (Ideal.Quotient.mk I) := by
    dsimp only [K]; rw [Ideal.map_span, Set.image_singleton]
  let eRing : ((A ⧸ I) ⧸ K) ≃+* (A ⧸ Ideal.span {j}) :=
    (Ideal.quotEquivOfEq hK).trans (DoubleQuot.quotQuotEquivQuotOfLE hle)
  have hsmul : K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))
      = Submodule.restrictScalars (A ⧸ I) (Ideal.map (algebraMap (A ⧸ I) (B ⧸ M)) K) :=
    Ideal.smul_top_eq_map K
  let f₀ : ((B ⧸ M) ⧸ K • (⊤ : Submodule (A ⧸ I) (B ⧸ M)))
      ≃ₗ[A ⧸ I] ((B ⧸ M) ⧸ Ideal.map (algebraMap (A ⧸ I) (B ⧸ M)) K) :=
    Submodule.quotEquivOfEq _ _ hsmul
  have hIJ : Ideal.map (algebraMap (A ⧸ I) (B ⧸ M)) K = Ideal.map (Ideal.Quotient.mk M) N := by
    dsimp only [K]
    rw [hN, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
  let f₁ : ((B ⧸ M) ⧸ Ideal.map (algebraMap (A ⧸ I) (B ⧸ M)) K)
      ≃+* ((B ⧸ M) ⧸ Ideal.map (Ideal.Quotient.mk M) N) := Ideal.quotEquivOfEq hIJ
  let f₂ : ((B ⧸ M) ⧸ Ideal.map (Ideal.Quotient.mk M) N) ≃+* (B ⧸ N) :=
    DoubleQuot.quotQuotEquivQuotOfLE hleM
  let f : ((B ⧸ M) ⧸ K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))) ≃+ (B ⧸ N) :=
    f₀.toAddEquiv.trans (f₁.toAddEquiv.trans f₂.toAddEquiv)
  have hf₀_eval : ∀ (x : B ⧸ M),
      f₀.toAddEquiv (Submodule.Quotient.mk (p := K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))) x)
        = Ideal.Quotient.mk (Ideal.map (algebraMap (A ⧸ I) (B ⧸ M)) K) x :=
    fun x => Submodule.quotEquivOfEq_mk _ _ hsmul x
  have hf₁_eval : ∀ (x : B ⧸ M),
      f₁.toAddEquiv (Ideal.Quotient.mk (Ideal.map (algebraMap (A ⧸ I) (B ⧸ M)) K) x)
        = Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk M) N) x :=
    fun x => Ideal.quotEquivOfEq_mk hIJ x
  have hf₂_eval : ∀ (b : B),
      f₂.toAddEquiv (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk M) N) (Ideal.Quotient.mk M b))
        = Ideal.Quotient.mk N b :=
    fun b => DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk b hleM
  have hf_eval : ∀ (z : B),
      f (Submodule.Quotient.mk (p := K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))) (Ideal.Quotient.mk M z))
        = Ideal.Quotient.mk N z := by
    intro z
    show f₂.toAddEquiv (f₁.toAddEquiv (f₀.toAddEquiv
      (Submodule.Quotient.mk (p := K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))) (Ideal.Quotient.mk M z))))
      = Ideal.Quotient.mk N z
    rw [hf₀_eval, hf₁_eval, hf₂_eval]
  have hf_eRing : ∀ (a : A), eRing (Ideal.Quotient.mk K (Ideal.Quotient.mk I a))
      = Ideal.Quotient.mk (Ideal.span {j}) a := by
    intro a
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (I := I) (J := Ideal.span {j}) a hle
  have hcompat : ∀ (r : (A ⧸ I) ⧸ K) (m : (B ⧸ M) ⧸ K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))),
      f (r • m) = eRing r • f m := by
    intro r m
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨xx, rfl⟩ := Submodule.Quotient.mk_surjective (K • (⊤ : Submodule (A ⧸ I) (B ⧸ M))) m
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective xx
    rw [Module.Quotient.mk_smul_mk, Ideal.Quotient.mk_smul_mk_quotient_map_quotient,
      hf_eval (algebraMap A B a * b), hf_eRing a, hf_eval b,
      Ideal.Quotient.mk_smul_mk_quotient_map_quotient]
  have hf : ∀ (s : A ⧸ Ideal.span {j}) (y : B ⧸ N),
      f.symm (s • y) = eRing.symm s • f.symm y := by
    intro s y
    apply f.injective
    simp only [AddEquiv.apply_symm_apply, hcompat, RingEquiv.apply_symm_apply]
  exact flat_congr eRing.symm f.symm hf h

/-- Hypothesis `h2` of the local flatness criterion for the FFP node: with `S = D ⧸ (p)ᵐ`, `I = (p̄) ⊆ S` and `T = D' ⧸ (p)ᵐD'`, the module `T ⧸ I • ⊤` is flat over `S ⧸ I`, granted that `D' ⧸ (p)D'` is faithfully flat over `D ⧸ (p)` (flatness is all that is used).

PLAN for the prover (write it at `Submission/Work/DSFFP/flat_quot_quot_pow.lean`).
For `m ≥ 1`, with `J := Ideal.span {(p : D) ^ m}` one has `I = (Ideal.span {(p : D)}).map (Ideal.Quotient.mk J)`, and
* `S ⧸ I = (D ⧸ J) ⧸ ((p).map (mk J)) ≃+* D ⧸ (p)` (the third-isomorphism result for ideals, e.g. by combining `Submodule.quotientQuotientEquivQuotient` with `Ideal.quotEquivOfEq`, or by an explicit `RingEquiv` through `Ideal.Quotient.lift`);
* `T ⧸ I • ⊤ = (D' ⧸ J.map (algebraMap D D')) ⧸ (p).map (algebraMap D D') ≃ₗ (D' ⧸ (p).map (algebraMap D D'))`, compatible with the ring isomorphism above (a `LinearEquiv` over that `RingEquiv`; `Submodule.quotientQuotientEquivQuotient` again), using `J.map (algebraMap D D') = Ideal.span {(p : D') ^ m}` and `I • ⊤ = (p) • (D' ⧸ J.map (algebraMap D D'))`.
Transport flatness across these isomorphisms: either build the transported `Module.Flat` instance through a `LinearEquiv` over the `RingEquiv` (flatness is preserved by linear isomorphisms, `Module.Flat.of_linearEquiv`/`Module.Flat.equiv_iff`, applied after rewriting the scalar structure), or prove `Module.Flat.iff_rTensor_injective` directly for the target and pull back along the two isomorphisms.  The hypothesis `h` provides `Module.Flat (D ⧸ (p)) (D' ⧸ (p).map (algebraMap D D'))`.
For `m = 0` the plan's isomorphism is false and unnecessary: `(p)^0 = 1`, so `S = D ⧸ ⊤` and `T = D' ⧸ ⊤` are subsingleton, and `Module.Flat` holds for trivial reasons (e.g. `infer_instance`, or `Module.Flat.iff_rTensor_injective` with `Subsingleton` both sides).  Handle `m = 0` separately. -/
theorem flat_quot_quot_pow {D D' : Type _} [CommRing D] [CommRing D'] [Algebra D D'] (p : ℕ)
    (h : Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D)})
      (D' ⧸ (Ideal.span {(p : D)}).map (algebraMap D D'))) (m : ℕ) :
    Module.Flat ((D ⧸ Ideal.span {(p : D) ^ m}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : D) ^ m}) (p : D)})
      ((D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D')) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : D) ^ m}) (p : D)} •
          (⊤ : Submodule (D ⧸ Ideal.span {(p : D) ^ m})
            (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D')))) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [pow_zero]
    have h1 : Ideal.span {(1:D)} = (⊤ : Ideal D) := Ideal.span_singleton_eq_top.mpr isUnit_one
    have hsub : Subsingleton (D' ⧸ (Ideal.span {(1:D)}).map (algebraMap D D')) := by
      rw [h1, Ideal.map_top]
      infer_instance
    haveI := hsub
    exact flat_of_subsingleton
  · refine flat_quot_quot_span (Ideal.span {(p:D)^m}) (p:D) ?_ h.toFlat
    rw [Ideal.span_singleton_le_span_singleton]
    simpa using pow_dvd_pow (p:D) (show 1 ≤ m by omega)

end Work.DSFFP
