import Mathlib
import Submission.Work.Serre.C1Cyl

/-!
# The mapping cylinder: explicit homeomorphism and homotopy equivalence

`Submission/Work/Serre/C1Cyl.lean` proves

* `Work.Serre.cylHomeo f : Nonempty (P ≃ₜ ↥(Set.range (cylIncl f)))`;
* `Work.Serre.cylHomotopyEquiv f : Nonempty (ContinuousMap.HomotopyEquiv (cyl f) X)`.

Both witnesses are constructed *explicitly* (`toFun = fun p => ⟨cylIncl f p, p, rfl⟩` and
`toFun = cylRetract f`), but the `Nonempty` wrapper hides that from a consumer: an appeal to
`Classical.choice` gives no information about `toFun`.  The C1 assembly needs the two *pointwise*
statements, so we re-run the two proofs here with the strengthened conclusions.

These are the only two facts from that file needed downstream; everything else is imported.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {P X : Type} [TopologicalSpace P] [TopologicalSpace X]

/-- **The bottom copy of the source is homeomorphic to the source, with an explicit `toFun`.**  The
homeomorphism is `p ↦ ⟨cylIncl f p, p, rfl⟩`, the (open) embedding of `P` as the bottom `P × {0}`
of the cylinder; the inverse is continuous because the cylinder supplies an open collar of that
copy.  This is `Work.Serre.cylHomeo` with its witness displayed. -/
theorem cylHomeoExplicit (f : C(P, X)) :
    ∃ e : P ≃ₜ ↥(Set.range (cylIncl f)), ∀ p : P, (e p : cyl f) = cylIncl f p := by
  classical
  have hq : Topology.IsQuotientMap (cylMk f) := isQuotientMap_quotient_mk'
  have hinj : Function.Injective (cylIncl f) := cylIncl_injective f
  -- the collar of the bottom copy, and its open image in the quotient
  let Collar : Set P → Set ((P × unitInterval) ⊕ X) := fun U =>
    Sum.inl '' (U ×ˢ {t : unitInterval | (t : ℝ) < 1})
  have hcollar : ∀ U : Set P, IsOpen U → IsOpen (cylMk f '' Collar U) := by
    intro U hU
    have hW₀ : IsOpen (Collar U) :=
      isOpenMap_inl _ (hU.prod (isOpen_lt continuous_subtype_val continuous_const))
    refine (hq.isOpen_preimage (s := cylMk f '' Collar U)).mp ?_
    have hpre : (cylMk f ⁻¹' (cylMk f '' Collar U)) = Collar U := by
      ext z
      constructor
      · rintro ⟨w, hw, hzw⟩
        rcases hw with ⟨q, hqU, rfl⟩
        obtain ⟨hqU₁, hqU₂⟩ := hqU
        have ht : q.2 ≠ 1 := by
          intro h
          rw [h] at hqU₂
          exact absurd hqU₂ (by norm_num)
        have hz : z = Sum.inl q := (eqvGen_inl_iff f ht (Quotient.exact hzw)).mp rfl
        rw [hz]
        exact ⟨q, ⟨hqU₁, hqU₂⟩, rfl⟩
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hpre]
    exact hW₀
  -- the inverse function of the homeomorphism
  let invFun : ↥(Set.range (cylIncl f)) → P := fun a => a.2.choose
  have hinv : ∀ a : ↥(Set.range (cylIncl f)), cylIncl f (invFun a) = a.1 :=
    fun a => a.2.choose_spec
  refine ⟨{ toFun := fun p => ⟨cylIncl f p, p, rfl⟩
            invFun := invFun
            left_inv := fun p => hinj (hinv ⟨cylIncl f p, p, rfl⟩)
            right_inv := fun a => Subtype.ext (hinv a)
            continuous_toFun := Continuous.subtype_mk (cylIncl f).continuous _
            continuous_invFun := ?_ }, fun p => rfl⟩
  rw [continuous_def]
  intro U hU
  change IsOpen (invFun ⁻¹' U)
  have heq : invFun ⁻¹' U = Subtype.val ⁻¹' (cylMk f '' Collar U) := by
    ext a
    constructor
    · intro ha
      exact ⟨Sum.inl (invFun a, 0), ⟨(invFun a, 0), ⟨ha, by norm_num⟩, rfl⟩, hinv a⟩
    · rintro ⟨w, hw, hwa⟩
      rcases hw with ⟨q, hqU, rfl⟩
      obtain ⟨hqU₁, hqU₂⟩ := hqU
      have ht : q.2 ≠ 1 := by
        intro h
        rw [h] at hqU₂
        exact absurd hqU₂ (by norm_num)
      have h2 : (Quotient.mk'' (Sum.inl (invFun a, 0)) : cyl f) =
          Quotient.mk'' (Sum.inl q) := (hinv a).trans hwa.symm
      have h3 : (Sum.inl (invFun a, 0) : (P × unitInterval) ⊕ X) = Sum.inl q :=
        (eqvGen_inl_iff f (p := q.1) (t := q.2) ht (Quotient.exact h2)).mpr rfl
      have h4 : invFun a = q.1 := by
        simpa using congrArg Prod.fst (Sum.inl.inj h3)
      show invFun a ∈ U
      exact h4.symm ▸ hqU₁
  rw [heq]
  exact (hcollar U hU).preimage continuous_subtype_val

/-- **The mapping cylinder is homotopy equivalent to its target, with an explicit `toFun`.**  The
homotopy equivalence is `cylRetract f` with inverse `cylInr f`; the homotopy pushing the cylinder
up to its top is `Work.Serre.cylMove`.  This is `Work.Serre.cylHomotopyEquiv` with its witness
displayed. -/
theorem cylHomotopyEquivExplicit (f : C(P, X)) :
    ∃ E : ContinuousMap.HomotopyEquiv (cyl f) X, E.toFun = cylRetract f := by
  refine ⟨ContinuousMap.HomotopyEquiv.mk (cylRetract f) (cylInr f) ?_ ?_, rfl⟩
  · exact ⟨{ toContinuousMap :=
                ⟨fun p : unitInterval × cyl f => cylMove f (p.2, unitIntervalOneSub p.1),
                  (cylMove f).continuous.comp
                    (continuous_snd.prodMk (continuous_unitIntervalOneSub.comp continuous_fst))⟩,
              map_zero_left := fun y => by simp [cylMove_one],
              map_one_left := fun y => by simp [cylMove_zero] }⟩
  · have hcomp : (cylRetract f).comp (cylInr f) = ContinuousMap.id X :=
      ContinuousMap.ext (fun x => rfl)
    simpa only [hcomp] using
      (show ((ContinuousMap.id X).Homotopic (ContinuousMap.id X)) from
        ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩)

end

end Work.Serre
