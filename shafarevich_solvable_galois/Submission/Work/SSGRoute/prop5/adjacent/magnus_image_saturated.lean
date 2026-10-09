import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.magnusLieDefs
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
import Submission.Work.SSGRoute.prop5.witt.hall_foliage_lt_right
import Submission.Work.SSGRoute.prop5.witt.Vocab
import Submission.Work.SSGRoute.prop5.witt.Swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Saturation of the Magnus image in the degree-`j` part

If `y` lies in the `j`-th term `γ_j` of the lower central series of a free group `F = FreeGroup X`
and the Magnus leading term of `y` (its component in the degree-`j` part of the free associative
algebra `FreeAssoc X = ℤ[FreeMonoid X]`, truncated at `fil X (j+1)`) equals `n · x`, then `x` is
itself the Magnus leading term of an element of `γ_j`.

Equivalently the image of `γ_j` in the degree-`j` part is a *saturated* (`pure`) subgroup.  The
proof has three ingredients.

* The image of `γ_j` in the degree-`j` part agrees with the degree-`j` part of the free Lie ring
  (`lieSpan`), the identification `lead_mem_lieSpan` / `exists_gamma_of_mem_lieSpan`.
* The degree-`j` part of the free Lie ring is spanned by the bracket monomials of the *Hall* trees
  of size `j` (Hall's spanning theorem, `witt.hall_spanning`).
* Those bracket monomials form a triangular family with distinct leading words
  (`witt.leading_term_coeff`, `witt.hall_foliage_injective`), hence span a direct summand of the
  degree-`j` part of the free associative algebra.
-/

noncomputable section

set_option maxHeartbeats 1000000

open scoped commutatorElement

attribute [local instance] Classical.propDecidable
attribute [local instance 100] LieRing.ofAssociativeRing

namespace Work.SSGRoute.prop5.adjacent

variable {X : Type*}

/-! ## The degree projection of the free associative algebra -/

/-- The projection of `FreeAssoc X = ℤ[FreeMonoid X]` onto the words of length `j` (the "degree
`j` part"). -/
noncomputable def degPart (j : ℕ) : FreeAssoc X →ₗ[ℤ] FreeAssoc X where
  toFun a := MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j) a.coeff)
  map_add' a b := by
    apply MonoidAlgebra.ext
    ext w
    show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
      (a + b).coeff)).coeff w = _
    rw [MonoidAlgebra.coeff_add, Finsupp.filter_add, Finsupp.add_apply]
    rfl
  map_smul' c a := by
    apply MonoidAlgebra.ext
    ext w
    show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
      (c • a).coeff)).coeff w = _
    rw [MonoidAlgebra.coeff_smul, Finsupp.filter_smul, Finsupp.smul_apply]
    rfl

theorem coeff_degPart (j : ℕ) (a : FreeAssoc X) (w : FreeMonoid X) :
    (degPart (X:=X) j a).coeff w = if w.length = j then a.coeff w else 0 := by
  show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
    a.coeff)).coeff w = _
  rw [Finsupp.filter_apply]

theorem coeff_single_fa (w v : FreeMonoid X) (r : ℤ) :
    (MonoidAlgebra.single w r : FreeAssoc X).coeff v = if v = w then r else 0 := by
  rw [MonoidAlgebra.coeff_single]
  by_cases h : v = w
  · subst h; rw [if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_eq_of_ne h]

theorem degPart_single (j : ℕ) (w : FreeMonoid X) (r : ℤ) :
    degPart (X:=X) j (MonoidAlgebra.single w r)
      = if w.length = j then MonoidAlgebra.single w r else 0 := by
  apply MonoidAlgebra.ext; ext v
  rw [coeff_degPart, coeff_single_fa]
  have hR : ((if w.length = j then (MonoidAlgebra.single w r : FreeAssoc X) else 0)).coeff v
      = (if w.length = j then (if v = w then r else 0) else 0) := by
    by_cases h : w.length = j
    · rw [if_pos h, if_pos h, coeff_single_fa]
    · rw [if_neg h, if_neg h, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  rw [hR]
  by_cases hv : v = w
  · subst hv; rfl
  · rw [if_neg hv]
    by_cases hw : w.length = j
    · rw [if_pos hw]; split_ifs <;> rfl
    · rw [if_neg hw]; split_ifs <;> rfl

theorem degPart_wordEl (j : ℕ) (w : List X) :
    degPart (X:=X) j (wordEl w) = if w.length = j then wordEl w else 0 := by
  rw [wordEl, degPart_single]
  rfl

theorem single_mem_wordSpan {j : ℕ} {w : FreeMonoid X} (h : w.length = j) (r : ℤ) :
    MonoidAlgebra.single w r ∈ wordSpan (X:=X) j := by
  rw [show MonoidAlgebra.single w r = r • MonoidAlgebra.single w (1:ℤ) by
    rw [MonoidAlgebra.smul_single']; simp]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨FreeMonoid.toList w, h, by rw [wordEl, FreeMonoid.ofList_toList]⟩

theorem degPart_mem_wordSpan (j : ℕ) (a : FreeAssoc X) :
    degPart (X:=X) j a ∈ wordSpan (X:=X) j := by
  have hsum := Finsupp.sum_of_support_subset (degPart (X:=X) j a).coeff
      (s := (degPart (X:=X) j a).coeff.support) (Finset.Subset.refl _)
      (fun w r => MonoidAlgebra.single w r) (fun i hi => by simp)
  rw [show (degPart (X:=X) j a).coeff.sum (fun w r => MonoidAlgebra.single w r) =
      degPart (X:=X) j a from MonoidAlgebra.sum_coeff_single _] at hsum
  rw [hsum]
  refine Submodule.sum_mem _ (fun w hw => ?_)
  have hwj : w.length = j := by
    by_contra hw'
    exact (Finsupp.mem_support_iff.mp hw) (by rw [coeff_degPart, if_neg hw'])
  exact single_mem_wordSpan hwj ((degPart (X:=X) j a).coeff w)

theorem mem_wordSpan_iff (j : ℕ) (a : FreeAssoc X) :
    a ∈ wordSpan (X:=X) j ↔ ∀ w : FreeMonoid X, w.length ≠ j → a.coeff w = 0 := by
  constructor
  · intro h
    refine Submodule.span_induction (p := fun a _ => ∀ w, w.length ≠ j → a.coeff w = 0)
      ?_ ?_ ?_ ?_ h
    · rintro a ⟨u, hu, rfl⟩ w hw
      rw [wordEl, coeff_single_fa, if_neg]
      intro h'
      exact hw (by rw [h']; exact hu)
    · intro w hw; rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro x y _ _ hx hy w hw
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx w hw, hy w hw, add_zero]
    · intro c x _ hx w hw
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hx w hw, smul_zero]
  · intro h
    have hsum := Finsupp.sum_of_support_subset a.coeff (s := a.coeff.support) (Finset.Subset.refl _)
        (fun w r => MonoidAlgebra.single w r) (fun i hi => by simp)
    rw [show a.coeff.sum (fun w r => MonoidAlgebra.single w r) = a
        from MonoidAlgebra.sum_coeff_single _] at hsum
    rw [hsum]
    refine Submodule.sum_mem _ (fun w hw => ?_)
    have hwj : w.length = j := by
      by_contra hw'
      exact (Finsupp.mem_support_iff.mp hw) (h w hw')
    exact single_mem_wordSpan hwj (a.coeff w)

theorem degPart_eq_self_of_mem_wordSpan {j : ℕ} {a : FreeAssoc X} (ha : a ∈ wordSpan (X:=X) j) :
    degPart (X:=X) j a = a := by
  apply MonoidAlgebra.ext; ext w
  rw [coeff_degPart]
  by_cases h : w.length = j
  · rw [if_pos h]
  · rw [if_neg h, (mem_wordSpan_iff j a).mp ha w h]

theorem wordSpan_mul_mem {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ wordSpan (X:=X) p) (hb : b ∈ wordSpan (X:=X) q) :
    a * b ∈ wordSpan (X:=X) (p+q) := by
  refine Submodule.span_induction₂ (p := fun a b _ _ => a * b ∈ wordSpan (X:=X) (p+q))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [wordEl, wordEl, MonoidAlgebra.single_mul_single, mul_one]
    rw [show MonoidAlgebra.single (FreeMonoid.ofList u * FreeMonoid.ofList v) (1:ℤ)
        = wordEl (u ++ v) by rw [wordEl, FreeMonoid.ofList_append]]
    exact Submodule.subset_span ⟨u ++ v, by rw [List.length_append, hu, hv], rfl⟩
  · intro y hy; rw [zero_mul]; exact Submodule.zero_mem _
  · intro x hx; rw [mul_zero]; exact Submodule.zero_mem _
  · intro x y z hx hy hz h1 h2; rw [add_mul]; exact Submodule.add_mem _ h1 h2
  · intro x y z hx hy hz h1 h2; rw [mul_add]; exact Submodule.add_mem _ h1 h2
  · intro r x y hx hy h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y hx hy h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

theorem mem_fil_of_mem_wordSpan {j : ℕ} {a : FreeAssoc X} (h : a ∈ wordSpan (X:=X) j) :
    a ∈ fil X j := by
  rw [wordSpan] at h
  rw [fil_eq_filI]
  change a ∈ Submodule.span ℤ (filgen X j)
  exact (Submodule.span_le.mpr (by
    rintro a ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨FreeMonoid.ofList u,
      by rw [show (FreeMonoid.ofList u).length = u.length from rfl, hu], rfl⟩)) h

theorem degPart_eq_zero_of_mem_fil {N j : ℕ} {a : FreeAssoc X} (h : a ∈ fil X N) (hN : j < N) :
    degPart (X:=X) j a = 0 := by
  rw [fil_eq_filI] at h
  change a ∈ Submodule.span ℤ (filgen X N) at h
  refine Submodule.span_induction (p := fun a _ => degPart (X:=X) j a = 0) ?_ ?_ ?_ ?_ h
  · rintro a ⟨w, hw, rfl⟩
    rw [degPart_single, if_neg (by omega)]
  · exact map_zero _
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro c x _ hx; rw [map_smul, hx, smul_zero]

theorem sub_degPart_mem_fil {p : ℕ} {a : FreeAssoc X} (h : a ∈ fil X p) :
    a - degPart (X:=X) p a ∈ fil X (p+1) := by
  rw [fil_eq_filI] at h ⊢
  change a ∈ Submodule.span ℤ (filgen X p) at h
  change a - degPart (X:=X) p a ∈ Submodule.span ℤ (filgen X (p+1))
  refine Submodule.span_induction (p := fun a _ => a - degPart (X:=X) p a ∈
      Submodule.span ℤ (filgen X (p+1))) ?_ ?_ ?_ ?_ h
  · rintro a ⟨w, hw, rfl⟩
    rw [degPart_single]
    by_cases hwj : w.length = p
    · rw [if_pos hwj, sub_self]; exact Submodule.zero_mem _
    · rw [if_neg hwj, sub_zero]
      exact Submodule.subset_span ⟨w, by omega, rfl⟩
  · rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    rw [show x + y - (degPart (X:=X) p x + degPart (X:=X) p y)
        = (x - degPart (X:=X) p x) + (y - degPart (X:=X) p y) from by abel]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    rw [show c • x - c • degPart (X:=X) p x = c • (x - degPart (X:=X) p x)
        from by rw [smul_sub]]
    exact Submodule.smul_mem _ c hx

theorem degPart_mul_of_mem_fil {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ fil X p) (hb : b ∈ fil X q) :
    degPart (X:=X) (p+q) (a * b) = degPart (X:=X) p a * degPart (X:=X) q b := by
  have ha' : a - degPart (X:=X) p a ∈ fil X (p+1) := sub_degPart_mem_fil ha
  have hb' : b - degPart (X:=X) q b ∈ fil X (q+1) := sub_degPart_mem_fil hb
  have hdpa : degPart (X:=X) p a ∈ fil X p := mem_fil_of_mem_wordSpan (degPart_mem_wordSpan p a)
  have hdqb : degPart (X:=X) q b ∈ fil X q := mem_fil_of_mem_wordSpan (degPart_mem_wordSpan q b)
  have hrest : a * b - degPart (X:=X) p a * degPart (X:=X) q b ∈ fil X (p+q+1) := by
    have heq : a * b - degPart (X:=X) p a * degPart (X:=X) q b
        = degPart (X:=X) p a * (b - degPart (X:=X) q b) + (a - degPart (X:=X) p a) * b := by
      noncomm_ring
    rw [heq]
    refine Submodule.add_mem _ ?_ ?_
    · exact fil_mul_le X p (q+1) (Ideal.mul_mem_mul hdpa hb')
    · have h := fil_mul_le X (p+1) q (Ideal.mul_mem_mul ha' hb)
      rwa [show (p+1)+q = p+q+1 from by omega] at h
  have h1 : degPart (X:=X) (p+q) (a * b - degPart (X:=X) p a * degPart (X:=X) q b) = 0 :=
    degPart_eq_zero_of_mem_fil hrest (by omega)
  have h2 : degPart (X:=X) (p+q) (a * b)
      = degPart (X:=X) (p+q) (degPart (X:=X) p a * degPart (X:=X) q b) := by
    rw [map_sub] at h1
    exact sub_eq_zero.mp h1
  rw [h2, degPart_eq_self_of_mem_wordSpan
    (wordSpan_mul_mem (degPart_mem_wordSpan p a) (degPart_mem_wordSpan q b))]

/-! ## The degree component of an element of a truncation -/

/-- A chosen representative of an element of the truncated algebra. -/
noncomputable def qrep (N : ℕ) (x : FreeAssoc X ⧸ fil X N) : FreeAssoc X :=
  (Ideal.Quotient.mk_surjective x).choose

theorem qrep_spec (N : ℕ) (x : FreeAssoc X ⧸ fil X N) :
    Ideal.Quotient.mk (fil X N) (qrep N x) = x :=
  (Ideal.Quotient.mk_surjective x).choose_spec

/-- The degree-`j` component of an element of the truncated free associative algebra. -/
noncomputable def qdeg (N j : ℕ) (x : FreeAssoc X ⧸ fil X N) : FreeAssoc X :=
  degPart (X:=X) j (qrep N x)

theorem qdeg_congr {N j : ℕ} (hj : j < N) {a b : FreeAssoc X}
    (h : Ideal.Quotient.mk (fil X N) a = Ideal.Quotient.mk (fil X N) b) :
    degPart (X:=X) j a = degPart (X:=X) j b := by
  have h' : a - b ∈ fil X N := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h, sub_self]
  have h0 : degPart (X:=X) j (a - b) = 0 := degPart_eq_zero_of_mem_fil h' hj
  rwa [map_sub, sub_eq_zero] at h0

theorem qdeg_eq_degPart {N j : ℕ} (hj : j < N) {a : FreeAssoc X}
    {x : FreeAssoc X ⧸ fil X N} (hx : Ideal.Quotient.mk (fil X N) a = x) :
    qdeg N j x = degPart (X:=X) j a :=
  qdeg_congr hj (by rw [qrep_spec, hx])

theorem qdeg_add {N j : ℕ} (hj : j < N) (x y : FreeAssoc X ⧸ fil X N) :
    qdeg N j (x + y) = qdeg N j x + qdeg N j y := by
  rw [qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N x + qrep N y)
      (x := x + y) (by rw [map_add, qrep_spec, qrep_spec])]
  rw [map_add, qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N x) (x := x) (qrep_spec N x),
    qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N y) (x := y) (qrep_spec N y)]

theorem qdeg_sub {N j : ℕ} (hj : j < N) (x y : FreeAssoc X ⧸ fil X N) :
    qdeg N j (x - y) = qdeg N j x - qdeg N j y := by
  rw [qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N x - qrep N y)
      (x := x - y) (by rw [map_sub, qrep_spec, qrep_spec])]
  rw [map_sub, qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N x) (x := x) (qrep_spec N x),
    qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N y) (x := y) (qrep_spec N y)]

theorem qdeg_smul {N j : ℕ} (hj : j < N) (c : ℤ) (x : FreeAssoc X ⧸ fil X N) :
    qdeg N j (c • x) = c • qdeg N j x := by
  rw [qdeg_eq_degPart (N := N) (j := j) hj (a := c • qrep N x)
      (x := c • x) (by rw [map_zsmul, qrep_spec])]
  rw [map_zsmul, qdeg_eq_degPart (N := N) (j := j) hj (a := qrep N x) (x := x) (qrep_spec N x)]

theorem qdeg_zero {N j : ℕ} (hj : j < N) : qdeg (X := X) N j 0 = 0 := by
  have h : qrep N (0 : FreeAssoc X ⧸ fil X N) ∈ fil X N := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, qrep_spec]
  rw [qdeg, degPart_eq_zero_of_mem_fil h hj]

theorem qdeg_eq_zero_of_mem_filq {N j k : ℕ} (hkN : k ≤ N) (hk : j < k) {x : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N k) : qdeg N j x = 0 := by
  obtain ⟨a, ha, rfl⟩ := mem_filq_iff.1 hx
  rw [qdeg_eq_degPart (N := N) (j := j) (by omega : j < N)
    (rfl : Ideal.Quotient.mk (fil X N) a = Ideal.Quotient.mk (fil X N) a)]
  exact degPart_eq_zero_of_mem_fil (filz_le_fil X k ha) hk

theorem qdeg_mem_wordSpan {N j : ℕ} (x : FreeAssoc X ⧸ fil X N) :
    qdeg N j x ∈ wordSpan (X:=X) j :=
  degPart_mem_wordSpan j _


/-! ## The projection between truncations -/

/-- The natural projection `A ⧸ fil X N' → A ⧸ fil X N` for `N ≤ N'`. -/
def projFil {N N' : ℕ} (h : N ≤ N') :
    (FreeAssoc X ⧸ fil X N') →+* (FreeAssoc X ⧸ fil X N) :=
  Ideal.Quotient.lift (fil X N') (Ideal.Quotient.mk (fil X N))
    (fun a ha => by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact fil_antitone X h ha)

theorem projFil_mk {N N' : ℕ} (h : N ≤ N') (a : FreeAssoc X) :
    projFil (X := X) h (Ideal.Quotient.mk (fil X N') a) = Ideal.Quotient.mk (fil X N) a :=
  Ideal.Quotient.lift_mk (fil X N') _ _

theorem projFil_magLead {N N' : ℕ} (h : N ≤ N') (z : FreeGroup X) :
    projFil (X := X) h (magLead N' z) = magLead N z := by
  have hhom : (Units.map (projFil (X := X) h).toMonoidHom).comp (magnus X N') = magnus X N := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    apply Units.ext
    rw [MonoidHom.comp_apply, Units.coe_map]
    show projFil (X := X) h (((magnus X N' (FreeGroup.of x) : (FreeAssoc X ⧸ fil X N')ˣ) :
      FreeAssoc X ⧸ fil X N')) = _
    rw [magnus_of, magnus_of, map_add, map_one, projFil_mk]
  have h2 : projFil (X := X) h (((magnus X N' z : (FreeAssoc X ⧸ fil X N')ˣ) :
      FreeAssoc X ⧸ fil X N')) = ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) :
      FreeAssoc X ⧸ fil X N) := by
    have := congrArg (fun f : FreeGroup X →* (FreeAssoc X ⧸ fil X N)ˣ =>
      ((f z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) hhom
    simpa [MonoidHom.comp_apply, Units.coe_map] using this
  rw [magLead, magLead, map_sub, map_one, h2]

theorem qdeg_projFil {N N' j : ℕ} (h : N ≤ N') (hj : j < N)
    (x : FreeAssoc X ⧸ fil X N') :
    qdeg (X := X) N' j x = qdeg (X := X) N j (projFil (X := X) h x) := by
  have hclass : Ideal.Quotient.mk (fil X N) (qrep N' x) =
      Ideal.Quotient.mk (fil X N) (qrep N (projFil (X := X) h x)) := by
    rw [← projFil_mk h (qrep N' x), qrep_spec N' x, qrep_spec N (projFil (X := X) h x)]
  have := qdeg_congr (N := N) (j := j) hj hclass
  rw [qdeg, qdeg]
  exact this

/-- The degree-`j` component of the Magnus leading term is independent of the truncation, as long
as the truncation exceeds `j`. -/
theorem qdeg_magLead_trunc {N N' j : ℕ} (h : N ≤ N') (hj : j < N) (z : FreeGroup X) :
    qdeg (X := X) N' j (magLead N' z) = qdeg (X := X) N j (magLead N z) := by
  rw [qdeg_projFil h hj (magLead N' z), projFil_magLead h z]

/-! ## Products of elements of filtration pieces -/

/-- The degree-`(p+q)` component of a product of an element of `filq X N p` with an element of
`filq X N q`. -/
theorem qdeg_mul_of_mem_filq {N p q : ℕ} (hpq : p + q < N) {x y : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N p) (hy : y ∈ filq X N q) :
    qdeg (X := X) N (p + q) (x * y) = qdeg (X := X) N p x * qdeg (X := X) N q y := by
  obtain ⟨A, hA, rfl⟩ := mem_filq_iff.1 hx
  obtain ⟨B, hB, rfl⟩ := mem_filq_iff.1 hy
  rw [← map_mul (Ideal.Quotient.mk (fil X N)) A B]
  rw [qdeg_eq_degPart (N := N) (j := p + q) hpq
    (rfl : Ideal.Quotient.mk (fil X N) (A * B) = _)]
  rw [degPart_mul_of_mem_fil (filz_le_fil X p hA) (filz_le_fil X q hB)]
  rw [qdeg_eq_degPart (N := N) (j := p) (by omega : p < N) (rfl : Ideal.Quotient.mk (fil X N) A = _),
    qdeg_eq_degPart (N := N) (j := q) (by omega : q < N) (rfl : Ideal.Quotient.mk (fil X N) B = _)]

theorem qdeg_mul_of_mem_filq' {N p q : ℕ} (hpq : p + q < N) {x y : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N p) (hy : y ∈ filq X N q) :
    qdeg (X := X) N (q + p) (x * y) = qdeg (X := X) N p x * qdeg (X := X) N q y := by
  rw [Nat.add_comm q p, qdeg_mul_of_mem_filq hpq hx hy]

theorem qdeg_neg {N j : ℕ} (hj : j < N) (x : FreeAssoc X ⧸ fil X N) :
    qdeg (X := X) N j (-x) = -qdeg (X := X) N j x := by
  have h : (0 : FreeAssoc X ⧸ fil X N) - x = -x := by abel
  rw [← h, qdeg_sub hj, qdeg_zero hj, zero_sub]

/-! ## Bracket monomials, the Lie span and the word span -/

theorem degPart_eq_zero_of_mem_wordSpan_of_ne {j k : ℕ} {a : FreeAssoc X}
    (ha : a ∈ wordSpan (X := X) k) (h : j ≠ k) : degPart (X := X) j a = 0 := by
  apply MonoidAlgebra.ext; ext w
  rw [coeff_degPart, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases hw : w.length = j
  · rw [if_pos hw]
    exact (mem_wordSpan_iff k a).mp ha w (by rw [hw]; exact h)
  · rw [if_neg hw]

/-- The bracket monomial of a tree lies in the word span of its size. -/
theorem monBrk_mem_wordSpan (c : Magma X) : monBrk X c ∈ wordSpan (X := X) (Magma.size c) := by
  induction c with
  | gen x => exact Submodule.subset_span ⟨[x], rfl, by simp [wordEl, monBrk_gen]⟩
  | mul a b iha ihb =>
      rw [monBrk_mul, Magma.size_mul]
      exact Submodule.sub_mem _
        (wordSpan_mul_mem (p := Magma.size a) (q := Magma.size b) iha ihb)
        (by simpa [Nat.add_comm] using
          wordSpan_mul_mem (p := Magma.size b) (q := Magma.size a) ihb iha)

/-- The `ℤ`-span of the bracket monomials of degree `j`: the degree-`j` part of the free Lie ring,
presented inside the free associative algebra. -/
def lieSpan (X : Type*) (j : ℕ) : Submodule ℤ (FreeAssoc X) :=
  Submodule.span ℤ {a : FreeAssoc X | ∃ c : Magma X, Magma.size c = j ∧ a = monBrk X c}

theorem monBrk_mem_lieSpan (c : Magma X) : monBrk X c ∈ lieSpan X (Magma.size c) :=
  Submodule.subset_span ⟨c, rfl, rfl⟩

theorem lieSpan_le_wordSpan (j : ℕ) : lieSpan X j ≤ wordSpan (X := X) j := by
  rw [lieSpan]
  refine Submodule.span_le.mpr ?_
  rintro a ⟨c, hc, rfl⟩
  rw [← hc]
  exact monBrk_mem_wordSpan c

/-- The Lie span is closed under the ring commutator. -/
theorem lieSpan_bracket_mem {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ lieSpan X p) (hb : b ∈ lieSpan X q) : a * b - b * a ∈ lieSpan X (p + q) := by
  refine Submodule.span_induction₂ (p := fun a b _ _ => a * b - b * a ∈ lieSpan X (p+q))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    rw [← hc, ← hd]
    exact Submodule.subset_span ⟨Magma.mul c d, by rw [Magma.size_mul], (monBrk_mul c d).symm⟩
  · intro y hy; rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
  · intro x hx; rw [mul_zero, zero_mul, sub_self]; exact Submodule.zero_mem _
  · intro x y z hx hy hz h1 h2
    rw [add_mul, mul_add,
      show x * z + y * z - (z * x + z * y)
        = (x * z - z * x) + (y * z - z * y) from by abel]
    exact Submodule.add_mem _ h1 h2
  · intro x y z hx hy hz h1 h2
    rw [mul_add, add_mul,
      show x * y + x * z - (y * x + z * x)
        = (x * y - y * x) + (x * z - z * x) from by abel]
    exact Submodule.add_mem _ h1 h2
  · intro r x y hx hy h; rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ r h
  · intro r x y hx hy h; rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    exact Submodule.smul_mem _ r h

theorem wordSpan_one_le_lieSpan : wordSpan (X := X) 1 ≤ lieSpan X 1 := by
  rw [wordSpan]
  refine Submodule.span_le.mpr ?_
  rintro a ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hu
  exact Submodule.subset_span ⟨Magma.gen x, rfl, by simp [wordEl, monBrk_gen]⟩

/-! ## The Lie span is spanned by the Hall bracket monomials -/

theorem monBrk_mem_hallSpan_of_size [LinearOrder X] (c : Magma X) :
    monBrk X c ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h ∧
      Magma.size h = Magma.size c} => monBrk X h.1)) := by
  have h1 : degPart (X := X) (Magma.size c) (monBrk X c) = monBrk X c :=
    degPart_eq_self_of_mem_wordSpan (monBrk_mem_wordSpan c)
  have key : ∀ a ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h} =>
        monBrk X h.1)),
      degPart (X := X) (Magma.size c) a ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X //
        IsHall h ∧ Magma.size h = Magma.size c} => monBrk X h.1)) := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => degPart (X := X) (Magma.size c) a ∈
      Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h ∧
        Magma.size h = Magma.size c} => monBrk X h.1))) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨h, rfl⟩
      by_cases hs : Magma.size h.1 = Magma.size c
      · rw [degPart_eq_self_of_mem_wordSpan (by rw [← hs]; exact monBrk_mem_wordSpan h.1)]
        exact Submodule.subset_span ⟨⟨h.1, h.2, hs⟩, rfl⟩
      · rw [degPart_eq_zero_of_mem_wordSpan_of_ne (monBrk_mem_wordSpan h.1) (Ne.symm hs)]
        exact Submodule.zero_mem _
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c' x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c' hx
  rw [← h1]
  exact key _ (witt.hall_spanning (monBrk X) (fun a b => monBrk_mul a b) c)

theorem lieSpan_le_hallSpan [LinearOrder X] (j : ℕ) :
    lieSpan X j ≤ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h ∧
      Magma.size h = j} => monBrk X h.1)) := by
  rw [lieSpan]
  refine Submodule.span_le.mpr ?_
  rintro a ⟨c, hc, rfl⟩
  rw [← hc]
  exact monBrk_mem_hallSpan_of_size c

theorem hallSpan_le_lieSpan [LinearOrder X] (j : ℕ) :
    Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} =>
      monBrk X h.1)) ≤ lieSpan X j := by
  refine Submodule.span_le.mpr ?_
  rintro a ⟨h, rfl⟩
  exact Submodule.subset_span ⟨h.1, h.2.2, rfl⟩

/-! ## A triangular family spans a direct summand of the word span -/

/-- The coefficient functional at a word, as a `ℤ`-linear map. -/
def coeffL (w : FreeMonoid X) : FreeAssoc X →ₗ[ℤ] ℤ where
  toFun a := a.coeff w
  map_add' a b := by
    show MonoidAlgebra.coeff (a + b) w = MonoidAlgebra.coeff a w + MonoidAlgebra.coeff b w
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c a := by
    show MonoidAlgebra.coeff (c • a) w = c • MonoidAlgebra.coeff a w
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]

theorem coeffL_ofList (w : List X) (a : FreeAssoc X) :
    coeffL (X := X) (FreeMonoid.ofList w) a = coeffF a w := rfl

/-- The smallest word occurring in the bracket monomial of a Hall tree is its foliage. -/
theorem monBrk_min_word [LinearOrder X] {c : Magma X} (hc : IsHall c) {w : List X}
    (hw : coeffF (monBrk X c) w ≠ 0) : Magma.foliage c ≤ w := by
  by_contra h
  exact hw ((witt.leading_term_coeff hc (fun a b hab =>
    swap_hall_of_crux (fun a b hab => witt.hall_foliage_lt_right hab) hab)).2 w (not_le.mp h))

/-- The bracket monomial of a Hall tree determines its foliage. -/
theorem monBrk_foliage_eq [LinearOrder X] {c d : Magma X} (hc : IsHall c) (hd : IsHall d)
    (h : monBrk X c = monBrk X d) : Magma.foliage c = Magma.foliage d := by
  have hswap : ∀ a b : Magma X, IsHall (Magma.mul a b) →
      Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a :=
    fun a b hab => swap_hall_of_crux (fun a b hab => witt.hall_foliage_lt_right hab) hab
  have h1 : coeffF (monBrk X d) (Magma.foliage c) ≠ 0 := by
    rw [← h, (witt.leading_term_coeff hc hswap).1]
    exact one_ne_zero
  have h2 : coeffF (monBrk X c) (Magma.foliage d) ≠ 0 := by
    rw [h, (witt.leading_term_coeff hd hswap).1]
    exact one_ne_zero
  exact le_antisymm (monBrk_min_word hc h2) (monBrk_min_word hd h1)

/-- The bracket monomial of a tree of size `j` lies in the degree-`j` part. -/
theorem monBrk_mem_wordSpan_of_size_eq {c : Magma X} {j : ℕ} (hc : Magma.size c = j) :
    monBrk X c ∈ wordSpan (X := X) j := by
  rw [← hc]
  exact monBrk_mem_wordSpan c

/-- **Purity of a triangular span.**  If a family `b` in the degree-`j` part has distinct leading
words `f i` (occurring with coefficient `1`, with nothing below), then the lattice it spans is
*saturated*. -/
theorem span_pure_of_triangular [LinearOrder X] {ι : Type*} (j : ℕ) (f : ι → List X)
    (hf : Function.Injective f) (b : ι → FreeAssoc X) (hb : Function.Injective b)
    (hdeg : ∀ i, b i ∈ wordSpan (X := X) j)
    (hlead : ∀ i, coeffF (b i) (f i) = 1)
    (hbelow : ∀ i w, w < f i → coeffF (b i) w = 0)
    (n : ℤ) (hn : n ≠ 0) (v : FreeAssoc X) (hv : v ∈ wordSpan (X := X) j)
    (h : n • v ∈ Submodule.span ℤ (Set.range b)) :
    v ∈ Submodule.span ℤ (Set.range b) := by
  classical
  obtain ⟨c, hcsupp, hc⟩ := Submodule.mem_span_set.mp h
  have hbij : Set.BijOn b (b ⁻¹' ↑c.support) ↑c.support :=
    ⟨fun x hx => hx, (fun x _ y _ hxy => hb hxy), fun m hm => by
      obtain ⟨i, hi⟩ := hcsupp hm
      exact ⟨i, by rw [Set.mem_preimage, hi]; exact hm, hi⟩⟩
  let c' : ι →₀ ℤ := Finsupp.comapDomain b c hbij.injOn
  have hsumL : c'.sum (fun i r => r • b i) = n • v := by
    have h1 : c'.sum (fun i r => r • b i) = c.sum (fun m r => r • m) :=
      Finsupp.sum_comapDomain b c (fun m r => r • m) hbij
    rw [h1, hc]
  have key : ∀ (m : ℕ) (u : FreeAssoc X) (s : Finset ι) (α : ι → ℤ), s.card = m →
      s.Nonempty → (∑ i ∈ s, α i • b i) = n • u → u ∈ Submodule.span ℤ (Set.range b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u s α hcard hsne hsum
      obtain ⟨i₀, hi₀, hmin⟩ := s.exists_min_image f hsne
      have hcoeff : coeffL (X := X) (FreeMonoid.ofList (f i₀)) (∑ i ∈ s, α i • b i)
          = coeffL (X := X) (FreeMonoid.ofList (f i₀)) (n • u) := by rw [hsum]
      have hsingle : coeffL (X := X) (FreeMonoid.ofList (f i₀)) (α i₀ • b i₀) = α i₀ := by
        rw [map_smul, coeffL_ofList, hlead i₀, smul_eq_mul, mul_one]
      have hsum_coeff : coeffL (X := X) (FreeMonoid.ofList (f i₀)) (∑ i ∈ s, α i • b i)
          = α i₀ := by
        rw [map_sum, ← hsingle]
        refine Finset.sum_eq_single
          (f := fun x => coeffL (X := X) (FreeMonoid.ofList (f i₀)) (α x • b x)) i₀ ?_ ?_
        · intro i hi hne
          have hlt : f i₀ < f i := lt_of_le_of_ne (hmin i hi) (fun hh => hne (hf hh.symm))
          rw [map_smul, coeffL_ofList, hbelow i (f i₀) hlt, smul_zero]
        · intro h; exact absurd hi₀ h
      have hα : α i₀ = n * coeffF u (f i₀) := by
        rw [← hsum_coeff, hcoeff, map_smul, coeffL_ofList, smul_eq_mul]
      have hstep : ∑ i ∈ s.erase i₀, α i • b i
          = n • (u - (coeffF u (f i₀)) • b i₀) := by
        have hsplit : ∑ i ∈ s, α i • b i
            = ∑ i ∈ s.erase i₀, α i • b i + α i₀ • b i₀ :=
          (Finset.sum_erase_add _ _ hi₀).symm
        rw [hsplit] at hsum
        have hfac : n • (u - (coeffF u (f i₀)) • b i₀) = n • u - α i₀ • b i₀ := by
          rw [smul_sub, ← mul_smul, ← hα]
        rw [hfac]
        exact eq_sub_of_add_eq hsum
      have hmem₀ : b i₀ ∈ Submodule.span ℤ (Set.range b) :=
        Submodule.subset_span (Set.mem_range_self i₀)
      rcases (s.erase i₀).eq_empty_or_nonempty with hem | hne
      · rw [hem, Finset.sum_empty] at hstep
        have hu0 : u - (coeffF u (f i₀)) • b i₀ = 0 := by
          by_contra hne0
          exact hn ((smul_eq_zero.mp hstep.symm).resolve_right hne0)
        rw [sub_eq_zero] at hu0
        rw [hu0]
        exact Submodule.smul_mem _ _ hmem₀
      · have hpos : 0 < m := by rw [← hcard]; exact Finset.card_pos.mpr hsne
        have hcard' : (s.erase i₀).card < m := by
          rw [Finset.card_erase_of_mem hi₀, hcard]
          exact Nat.sub_lt hpos Nat.one_pos
        have hrec := ih (s.erase i₀).card hcard' (u - (coeffF u (f i₀)) • b i₀)
          (s.erase i₀) α rfl hne hstep
        have husplit : u = (u - (coeffF u (f i₀)) • b i₀) + (coeffF u (f i₀)) • b i₀ := by
          abel
        rw [husplit]
        exact Submodule.add_mem _ hrec (Submodule.smul_mem _ _ hmem₀)
  have hsum : ∑ i ∈ c'.support, c' i • b i = n • v := by
    rw [← Finsupp.sum_of_support_subset c' (Finset.Subset.refl _) (fun i r => r • b i) (by simp)]
    exact hsumL
  rcases c'.support.eq_empty_or_nonempty with hem | hne
  · rw [hem, Finset.sum_empty] at hsum
    have : v = 0 := by
      by_contra hv0
      exact hn ((smul_eq_zero.mp hsum.symm).resolve_right hv0)
    rw [this]; exact Submodule.zero_mem _
  · exact key c'.support.card v c'.support c' rfl hne hsum

/-! ## Saturation of the Lie span -/

/-- **The Lie span is saturated** in the degree-`j` part of the free associative algebra. -/
theorem lieSpan_pure [LinearOrder X] (j : ℕ) {n : ℤ} (hn : n ≠ 0) {v : FreeAssoc X}
    (hv : v ∈ wordSpan (X := X) j) (h : n • v ∈ lieSpan X j) : v ∈ lieSpan X j := by
  have hle := lieSpan_le_hallSpan (X := X) j
  have h1 : n • v ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h ∧
      Magma.size h = j} => monBrk X h.1)) := hle h
  have hswap : ∀ a b : Magma X, IsHall (Magma.mul a b) →
      Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a :=
    fun a b hab => swap_hall_of_crux (fun a b hab => witt.hall_foliage_lt_right hab) hab
  have h2 : v ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h ∧
      Magma.size h = j} => monBrk X h.1)) :=
    span_pure_of_triangular (X := X) j
      (fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} => Magma.foliage h.1)
      (fun a b hab => Subtype.ext (witt.hall_foliage_injective_aux a.2.1 b.2.1 hab))
      (fun h => monBrk X h.1)
      (fun a b hab => Subtype.ext (witt.hall_foliage_injective_aux a.2.1 b.2.1
        (monBrk_foliage_eq a.2.1 b.2.1 hab)))
      (fun h => monBrk_mem_wordSpan_of_size_eq h.2.2)
      (fun h => (witt.leading_term_coeff h.2.1 hswap).1)
      (fun h w hw => (witt.leading_term_coeff h.2.1 hswap).2 w hw)
      n hn v hv h1
  exact hallSpan_le_lieSpan j h2

/-! ## Realizing the Lie span by group commutators -/

/-- The group commutator evaluation of a binary tree. -/
def gpTree (X : Type*) : Magma X → FreeGroup X
  | .gen x => FreeGroup.of x
  | .mul a b => ⁅gpTree X a, gpTree X b⁆

theorem gpTree_mem (c : Magma X) :
    gpTree X c ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (Magma.size c - 1) := by
  induction c with
  | gen x => exact Subgroup.mem_top _
  | mul a b iha ihb =>
      have h := Subgroup.commutator_mem_commutator iha ihb
      have hle := commutator_lowerCentralSeries_le (FreeGroup X) (Magma.size a - 1)
        (Magma.size b - 1)
      have hidx : (Magma.size a - 1) + (Magma.size b - 1) + 1
          = Magma.size a + Magma.size b - 1 := by
        have := Magma.size_pos a; have := Magma.size_pos b; omega
      rw [hidx] at hle
      show ⁅gpTree X a, gpTree X b⁆ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries
        (Magma.size a + Magma.size b - 1)
      exact hle h

/-- The degree-`(size c)` component of the Magnus image of the group commutator evaluation of a
tree `c` is its bracket monomial. -/
theorem qdeg_magLead_gpTree (c : Magma X) {N : ℕ} (hN : Magma.size c < N) :
    qdeg (X := X) N (Magma.size c) (magLead N (gpTree X c)) = monBrk X c := by
  induction c with
  | gen x =>
      have hN1 : 1 < N := by simpa [Magma.size_gen] using hN
      rw [show gpTree X (Magma.gen x) = FreeGroup.of x from rfl,
        show Magma.size (Magma.gen x) = 1 from rfl]
      rw [qdeg_eq_degPart (N := N) (j := 1) (by omega)
        (a := MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ))
        (x := magLead N (FreeGroup.of x)) (by rw [magLead_of, wordEl]; simp)]
      rw [monBrk_gen, degPart_single, if_pos (by simp)]
  | mul a b iha ihb =>
      have hsa : 1 ≤ Magma.size a := Magma.size_pos a
      have hsb : 1 ≤ Magma.size b := Magma.size_pos b
      have hsum_lt : Magma.size a + Magma.size b < N := by
        simpa [Magma.size_mul] using hN
      have hca : Magma.size a < N := by omega
      have hcb : Magma.size b < N := by omega
      rw [show gpTree X (Magma.mul a b) = ⁅gpTree X a, gpTree X b⁆ from rfl,
        show Magma.size (Magma.mul a b) = Magma.size a + Magma.size b from rfl]
      have hb := magLead_commutator N (Magma.size a) (Magma.size b) hsa hsb (by omega)
        (gpTree_mem a) (gpTree_mem b)
      have hz : magLead N ⁅gpTree X a, gpTree X b⁆
          - (magLead N (gpTree X a) * magLead N (gpTree X b)
            - magLead N (gpTree X b) * magLead N (gpTree X a))
          ∈ filq X N (Magma.size a + Magma.size b + 1) := hb
      have heq : magLead N ⁅gpTree X a, gpTree X b⁆
          = (magLead N (gpTree X a) * magLead N (gpTree X b)
              - magLead N (gpTree X b) * magLead N (gpTree X a))
            + (magLead N ⁅gpTree X a, gpTree X b⁆
              - (magLead N (gpTree X a) * magLead N (gpTree X b)
                - magLead N (gpTree X b) * magLead N (gpTree X a))) := by abel
      rw [heq, qdeg_add (by omega : Magma.size a + Magma.size b < N),
        qdeg_eq_zero_of_mem_filq (by omega : Magma.size a + Magma.size b + 1 ≤ N) (by omega) hz,
        add_zero, qdeg_sub (by omega : Magma.size a + Magma.size b < N)]
      have hU : magLead N (gpTree X a) ∈ filq X N (Magma.size a) :=
        magLead_mem_filq N (Magma.size a) hsa (by omega) (gpTree_mem a)
      have hV : magLead N (gpTree X b) ∈ filq X N (Magma.size b) :=
        magLead_mem_filq N (Magma.size b) hsb (by omega) (gpTree_mem b)
      rw [qdeg_mul_of_mem_filq (N := N) (p := Magma.size a) (q := Magma.size b) (by omega) hU hV,
        qdeg_mul_of_mem_filq' (N := N) (p := Magma.size b) (q := Magma.size a) (by omega) hV hU,
        iha hca, ihb hcb, monBrk_mul]

/-- The degree-`j` component of an element of `filq X (j+1) j` determines it. -/
theorem eq_mk_qdeg_of_mem_filq {N k : ℕ} (hN : N = k + 1) {x : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N k) :
    Ideal.Quotient.mk (fil X N) (qdeg (X := X) N k x) = x := by
  obtain ⟨a, ha, rfl⟩ := mem_filq_iff.1 hx
  have h1 : qdeg (X := X) N k (Ideal.Quotient.mk (fil X N) a) = degPart (X := X) k a :=
    qdeg_eq_degPart (N := N) (j := k) (by omega) rfl
  rw [h1, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have h2 : degPart (X := X) k a - a ∈ fil X N := by
    have h := neg_mem (sub_degPart_mem_fil (filz_le_fil X k ha))
    rw [neg_sub] at h
    rwa [← hN] at h
  exact h2

/-! ## The Magnus image of `γ_j` is the degree-`j` part of the free Lie ring -/

theorem lead_mem_lieSpan : ∀ j : ℕ, 1 ≤ j →
    ∀ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
      qdeg (X := X) (j + 1) j (magLead (j + 1) z) ∈ lieSpan X j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ m ih =>
    intro hm z hz
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      exact wordSpan_one_le_lieSpan (qdeg_mem_wordSpan (X := X) (N := 2) (j := 1) (magLead 2 z))
    · have hzclos : z ∈ Subgroup.closure {g : FreeGroup X |
          ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m - 1),
          ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g} := by
        rw [← Subgroup.commutator_def, ← Subgroup.lowerCentralSeries_succ (n := m - 1),
          show m - 1 + 1 = m from by omega]
        exact hz
      have hmem : ∀ g ∈ Subgroup.closure {g : FreeGroup X |
            ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m - 1),
            ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g},
          g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := by
        intro g hg
        have h1 : Subgroup.closure {g : FreeGroup X |
              ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m - 1),
              ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g}
            ≤ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := by
          rw [Subgroup.closure_le]
          rintro x ⟨g1, hg1, g2, hg2, rfl⟩
          have h2 : ⁅g1, g2⁆ ∈ ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m - 1),
              (⊤ : Subgroup (FreeGroup X))⁆ :=
            Subgroup.commutator_mem_commutator hg1 hg2
          rw [← Subgroup.lowerCentralSeries_succ (n := m - 1),
            show m - 1 + 1 = m from by omega] at h2
          exact h2
        exact h1 hg
      refine Subgroup.closure_induction (p := fun z _ => qdeg (X := X) (m + 2) (m + 1)
        (magLead (m + 2) z) ∈ lieSpan X (m + 1)) ?_ ?_ ?_ ?_ hzclos
      · rintro z ⟨u, hu, v, hv, rfl⟩
        have hv' : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (1 - 1) := by
          rw [Nat.sub_self, Subgroup.lowerCentralSeries_zero]; exact hv
        have hb := magLead_commutator (m + 2) m 1 (by omega) le_rfl (by omega) hu hv'
        have hb' : magLead (m + 2) ⁅u, v⁆
            - (magLead (m + 2) u * magLead (m + 2) v
              - magLead (m + 2) v * magLead (m + 2) u) ∈ filq X (m + 2) (m + 2) := by
          simpa using hb
        have h0 : magLead (m + 2) ⁅u, v⁆
            = magLead (m + 2) u * magLead (m + 2) v
              - magLead (m + 2) v * magLead (m + 2) u :=
          sub_eq_zero.mp (mem_filq_self_eq_zero' hb')
        rw [h0, qdeg_sub (by omega : m + 1 < m + 2)]
        have hU : magLead (m + 2) u ∈ filq X (m + 2) m :=
          magLead_mem_filq (m + 2) m (by omega) (by omega) hu
        have hV : magLead (m + 2) v ∈ filq X (m + 2) 1 :=
          magLead_mem_filq (m + 2) 1 le_rfl (by omega) hv'
        rw [qdeg_mul_of_mem_filq (N := m + 2) (p := m) (q := 1) (by omega) hU hV,
          qdeg_mul_of_mem_filq' (N := m + 2) (p := 1) (q := m) (by omega) hV hU]
        have hA : qdeg (X := X) (m + 2) m (magLead (m + 2) u) ∈ lieSpan X m := by
          rw [qdeg_magLead_trunc (X := X) (N := m + 1) (N' := m + 2) (j := m) (by omega)
            (by omega) u]
          exact ih hmpos u hu
        have hB : qdeg (X := X) (m + 2) 1 (magLead (m + 2) v) ∈ lieSpan X 1 :=
          wordSpan_one_le_lieSpan (qdeg_mem_wordSpan (X := X) (N := m + 2) (j := 1) _)
        exact lieSpan_bracket_mem hA hB
      · rw [magLead_one, qdeg_zero (by omega : m + 1 < m + 2)]
        exact Submodule.zero_mem _
      · intro z1 z2 hz1 hz2 ih1 ih2
        rw [magLead_mul (m + 2) (m + 1) (by omega) (by omega) (by omega) (hmem z1 hz1)
            (hmem z2 hz2),
          qdeg_add (by omega : m + 1 < m + 2)]
        exact Submodule.add_mem _ ih1 ih2
      · intro z hz ihz
        rw [magLead_inv (m + 2) (m + 1) (by omega) (by omega) (by omega) (hmem z hz),
          qdeg_neg (by omega : m + 1 < m + 2)]
        exact Submodule.neg_mem _ ihz

/-- Every element of the Lie span of degree `j` is the Magnus leading term of an element of
`γ_j`. -/
theorem exists_gamma_of_mem_lieSpan (j : ℕ) (hj : 1 ≤ j) {a : FreeAssoc X}
    (ha : a ∈ lieSpan X j) :
    ∃ w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
      magLead (j + 1) w = (Ideal.Quotient.mk (fil X (j + 1))) a := by
  revert a
  refine Submodule.span_induction (R := ℤ) (s := {a : FreeAssoc X |
    ∃ c : Magma X, Magma.size c = j ∧ a = monBrk X c}) ?_ ?_ ?_ ?_
  · rintro a ⟨c, hc, rfl⟩
    have hjc : Magma.size c < j + 1 := by omega
    refine ⟨gpTree X c, ?_, ?_⟩
    · rw [← hc]; exact gpTree_mem c
    · have hq := qdeg_magLead_gpTree c (N := j + 1) hjc
      have hmem : magLead (j + 1) (gpTree X c) ∈ filq X (j + 1) (Magma.size c) :=
        magLead_mem_filq (j + 1) (Magma.size c) (by omega) (by omega) (gpTree_mem c)
      have hthis := eq_mk_qdeg_of_mem_filq (X := X) (N := j + 1) (k := Magma.size c)
        (by omega) hmem
      rw [← hthis, hq]
  · exact ⟨1, Subgroup.one_mem _, by rw [magLead_one, map_zero]⟩
  · rintro a b _ _ ⟨w₁, hw₁, he₁⟩ ⟨w₂, hw₂, he₂⟩
    refine ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, ?_⟩
    rw [magLead_mul (j + 1) j hj (by omega) (by omega) hw₁ hw₂, he₁, he₂, map_add]
  · rintro c a _ ⟨w, hw, he⟩
    rcases lt_or_ge 0 c with hc | hc
    · refine ⟨w ^ c.toNat, Subgroup.pow_mem _ hw _, ?_⟩
      have hc' : ((c.toNat : ℤ)) = c := Int.toNat_of_nonneg (le_of_lt hc)
      rw [magLead_pow (j + 1) j c.toNat hj (by omega) (by omega) hw, he, hc', map_zsmul,
        zsmul_eq_mul]
    · refine ⟨(w ^ (-c).toNat)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _), ?_⟩
      have hc'' : (((-c).toNat : ℤ)) = -c := Int.toNat_of_nonneg (by omega)
      rw [magLead_inv (j + 1) j hj (by omega) (by omega) (Subgroup.pow_mem _ hw _),
        magLead_pow (j + 1) j (-c).toNat hj (by omega) (by omega) hw, he, hc'', map_zsmul,
        zsmul_eq_mul]
      have hcast : (((-c : ℤ)) : FreeAssoc X ⧸ fil X (j + 1))
          = -(c : FreeAssoc X ⧸ fil X (j + 1)) := by push_cast; ring_nf
      rw [hcast, ← neg_mul, neg_neg]

/-! ## The word span meets the next filtration piece trivially -/

theorem wordSpan_inf_fil_eq_bot (j : ℕ) {a : FreeAssoc X} (ha : a ∈ wordSpan (X := X) j)
    (hb : a ∈ fil X (j + 1)) : a = 0 := by
  rw [← degPart_eq_self_of_mem_wordSpan ha,
    degPart_eq_zero_of_mem_fil hb (by omega : j < j + 1)]

/-! ## The main theorem -/

theorem magnus_image_saturated (X : Type) (n j : ℕ) (hn : 0 < n) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (x : Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))
    (hx : x ∈ Work.SSGRoute.prop5.filq X (j + 1) j)
    (h : ((Work.SSGRoute.prop5.magnus X (j + 1) y : (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
        Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) - 1 = (n : ℤ) * x) :
    ∃ w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
      ((Work.SSGRoute.prop5.magnus X (j + 1) w : (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) - 1 = x := by
  haveI hdec : DecidableRel (α := X) WellOrderingRel := fun a b => Classical.propDecidable _
  letI : LinearOrder X := linearOrderOfSTO WellOrderingRel
  have hmag : magLead (j + 1) y ∈ filq X (j + 1) j :=
    magLead_mem_filq (j + 1) j hj (by omega : j ≤ j + 1) hy
  have ha : qdeg (X := X) (j + 1) j (magLead (j + 1) y) ∈ lieSpan X j :=
    lead_mem_lieSpan j hj y hy
  obtain ⟨a₀, ha₀, ha₀eq⟩ := mem_filq_iff.1 hx
  have hA₀ : a₀ ∈ fil X j := filz_le_fil X j ha₀
  have hmkv : Ideal.Quotient.mk (fil X (j + 1)) (degPart (X := X) j a₀) = x := by
    rw [← ha₀eq, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have h := neg_mem (sub_degPart_mem_fil hA₀)
    rwa [neg_sub] at h
  have hnv : (n : ℤ) • degPart (X := X) j a₀
      = qdeg (X := X) (j + 1) j (magLead (j + 1) y) := by
    have h1 : Ideal.Quotient.mk (fil X (j + 1)) ((n : ℤ) • degPart (X := X) j a₀)
        = Ideal.Quotient.mk (fil X (j + 1))
            (qdeg (X := X) (j + 1) j (magLead (j + 1) y)) := by
      rw [map_zsmul, hmkv, eq_mk_qdeg_of_mem_filq (X := X) (N := j + 1) (k := j)
        rfl hmag,
        show magLead (j + 1) y = ((magnus X (j + 1) y :
          (FreeAssoc X ⧸ fil X (j + 1))ˣ) : FreeAssoc X ⧸ fil X (j + 1)) - 1 from rfl, h,
        zsmul_eq_mul]
    have h2 : (n : ℤ) • degPart (X := X) j a₀
        - qdeg (X := X) (j + 1) j (magLead (j + 1) y) ∈ wordSpan (X := X) j :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ (degPart_mem_wordSpan j a₀))
        (lieSpan_le_wordSpan j ha)
    have h3 : (n : ℤ) • degPart (X := X) j a₀
        - qdeg (X := X) (j + 1) j (magLead (j + 1) y) ∈ fil X (j + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
    exact sub_eq_zero.mp (wordSpan_inf_fil_eq_bot (X := X) j h2 h3)
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have hvlie : degPart (X := X) j a₀ ∈ lieSpan X j :=
    lieSpan_pure j hnz (degPart_mem_wordSpan j a₀) (by rw [hnv]; exact ha)
  obtain ⟨w, hw, hwmem⟩ := exists_gamma_of_mem_lieSpan j hj hvlie
  refine ⟨w, hw, ?_⟩
  show magLead (j + 1) w = x
  rw [hwmem, hmkv]

end Work.SSGRoute.prop5.adjacent
