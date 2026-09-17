import Mathlib
import Submission.Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Triangular spanning for Lie algebras with triangular structure constants

This is the general form of the spanning half of the triangular (PBW) decomposition, used in
the `e₈` development: let `L` be a Lie algebra over a commutative ring `R`, let `H, E, F` be
three families of elements of `L` indexed by `κ`, satisfying

* `⁅Hᵢ, Eⱼ⁆ = Aᵢⱼ • Eⱼ`,
* `⁅Hᵢ, Fⱼ⁆ = -(Aᵢⱼ) • Fⱼ`,
* `⁅Eᵢ, Fⱼ⁆ = if i = j then Hᵢ else 0`,

and suppose that `H, E, F` generate `L` as a Lie algebra.  Then the universal enveloping
algebra `U(L)` is spanned by the *triangular monomials* `(F-word) · (H-word) · (E-word)`,
i.e.

`Submodule.span R (Set.range (fun p : List κ × List κ × List κ => Fw p.1 * Hw p.2.1 * Ew p.2.2)) = ⊤`.

The proof needs no PBW theorem.  It shows that the set `T` of triangular monomials is such
that the elements of `U(L)` acting on `T` from the right by multiplication are exactly the
elements of a subalgebra of `U(L)` containing `ι(L)`, hence all of `U(L)` (as `ι(L)` generates
`U(L)` as an `R`-algebra); applying this to the unit `1 ∈ T` gives `T = ⊤`.

The moving lemmas are list inductions moving a generator to the left through a word, using the
three commutation relations above.
-/

namespace Commons.Algebra.Lie.TriangularSpan

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section Words

variable (R : Type*) [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L] {κ : Type*}

/-- The product of the `ι`-images of the letters of a word, in a family `F`. -/
def Fword (F : κ → L) (w : List κ) : UniversalEnvelopingAlgebra R L :=
  (w.map (fun i => UniversalEnvelopingAlgebra.ι R (F i))).prod

/-- The product of the `ι`-images of the letters of a word, in a family `H`. -/
def Hword (H : κ → L) (w : List κ) : UniversalEnvelopingAlgebra R L :=
  (w.map (fun i => UniversalEnvelopingAlgebra.ι R (H i))).prod

/-- The product of the `ι`-images of the letters of a word, in a family `E`. -/
def Eword (E : κ → L) (w : List κ) : UniversalEnvelopingAlgebra R L :=
  (w.map (fun i => UniversalEnvelopingAlgebra.ι R (E i))).prod

@[simp] lemma Fword_nil (F : κ → L) : Fword R F ([] : List κ) = 1 := by simp [Fword]

@[simp] lemma Fword_cons (F : κ → L) (i : κ) (w : List κ) :
    Fword R F (i :: w) = UniversalEnvelopingAlgebra.ι R (F i) * Fword R F w := by
  simp [Fword]

@[simp] lemma Fword_singleton (F : κ → L) (i : κ) :
    Fword R F [i] = UniversalEnvelopingAlgebra.ι R (F i) := by
  simp [Fword]

lemma Fword_append (F : κ → L) (w w' : List κ) :
    Fword R F (w ++ w') = Fword R F w * Fword R F w' := by
  simp [Fword, List.map_append, List.prod_append]

@[simp] lemma Hword_nil (H : κ → L) : Hword R H ([] : List κ) = 1 := by simp [Hword]

@[simp] lemma Hword_cons (H : κ → L) (i : κ) (w : List κ) :
    Hword R H (i :: w) = UniversalEnvelopingAlgebra.ι R (H i) * Hword R H w := by
  simp [Hword]

@[simp] lemma Hword_singleton (H : κ → L) (i : κ) :
    Hword R H [i] = UniversalEnvelopingAlgebra.ι R (H i) := by
  simp [Hword]

lemma Hword_append (H : κ → L) (w w' : List κ) :
    Hword R H (w ++ w') = Hword R H w * Hword R H w' := by
  simp [Hword, List.map_append, List.prod_append]

@[simp] lemma Eword_nil (E : κ → L) : Eword R E ([] : List κ) = 1 := by simp [Eword]

@[simp] lemma Eword_cons (E : κ → L) (i : κ) (w : List κ) :
    Eword R E (i :: w) = UniversalEnvelopingAlgebra.ι R (E i) * Eword R E w := by
  simp [Eword]

@[simp] lemma Eword_singleton (E : κ → L) (i : κ) :
    Eword R E [i] = UniversalEnvelopingAlgebra.ι R (E i) := by
  simp [Eword]

lemma Eword_append (E : κ → L) (w w' : List κ) :
    Eword R E (w ++ w') = Eword R E w * Eword R E w' := by
  simp [Eword, List.map_append, List.prod_append]

/-- A triangular monomial: `(F-word) * (H-word) * (E-word)`. -/
def triMon (H E F : κ → L) (w v u : List κ) : UniversalEnvelopingAlgebra R L :=
  Fword R F w * Hword R H v * Eword R E u

/-- The `R`-span of the `H`-words. -/
def HwordSpan (H : κ → L) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R (Set.range (Hword R H))

/-- The `R`-span of the products `(H-word) * (E-word)`. -/
def HEspan (H E : κ → L) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R (Set.range (fun p : List κ × List κ => Hword R H p.1 * Eword R E p.2))

/-- The `R`-span of the triangular monomials. -/
def triSpan (H E F : κ → L) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R
    (Set.range (fun p : List κ × List κ × List κ => triMon R H E F p.1 p.2.1 p.2.2))

/-- The sum of the structure constants `A i j` over the letters `j` of the word `w`. -/
def cartSum (A : κ → κ → R) (i : κ) (w : List κ) : R := (w.map (A i)).sum

@[simp] lemma cartSum_nil (A : κ → κ → R) (i : κ) : cartSum R A i [] = 0 := by simp [cartSum]

@[simp] lemma cartSum_cons (A : κ → κ → R) (i j : κ) (w : List κ) :
    cartSum R A i (j :: w) = A i j + cartSum R A i w := by simp [cartSum]

end Words

section Main

variable (R : Type*) [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L] {κ : Type*}
  [DecidableEq κ] {A : κ → κ → R} {H E F : κ → L}

/-- The commutator identity in `U(L)`: `ι x * ι y - ι y * ι x = ι ⁅x, y⁆`. -/
lemma iota_mul_sub (x y : L) :
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y
      - UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x
      = UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ := by
  rw [← Ring.lie_def, ← LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) x y]

/-- `eᵢ * hⱼ = hⱼ * eᵢ - Aⱼᵢ • eᵢ` in `U(L)`, where `eᵢ = ι(Eᵢ)`, `hⱼ = ι(Hⱼ)`
(Cartan index `j`, raising index `i`). -/
lemma Eimg_mul_Himg (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (i j : κ) :
    UniversalEnvelopingAlgebra.ι R (E i) * UniversalEnvelopingAlgebra.ι R (H j) =
      UniversalEnvelopingAlgebra.ι R (H j) * UniversalEnvelopingAlgebra.ι R (E i)
        - A j i • UniversalEnvelopingAlgebra.ι R (E i) := by
  have h := iota_mul_sub (R := R) (H j) (E i)
  rw [hHE j i, map_smul, sub_eq_iff_eq_add'] at h
  rw [eq_sub_iff_add_eq]
  exact h.symm

/-- `hⱼ * fᵢ = fᵢ * hⱼ - Aⱼᵢ • fᵢ` in `U(L)` (Cartan index `j`, lowering index `i`). -/
lemma Himg_mul_Fimg (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j) • F j) (i j : κ) :
    UniversalEnvelopingAlgebra.ι R (H j) * UniversalEnvelopingAlgebra.ι R (F i) =
      UniversalEnvelopingAlgebra.ι R (F i) * UniversalEnvelopingAlgebra.ι R (H j)
        - A j i • UniversalEnvelopingAlgebra.ι R (F i) := by
  have h := iota_mul_sub (R := R) (H j) (F i)
  rw [hHF j i, map_smul, sub_eq_iff_eq_add', neg_smul, ← sub_eq_add_neg] at h
  exact h

/-- `eᵢ * fⱼ = fⱼ * eᵢ + δᵢⱼ hᵢ` in `U(L)`. -/
lemma Eimg_mul_Fimg (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0) (i j : κ) :
    UniversalEnvelopingAlgebra.ι R (E i) * UniversalEnvelopingAlgebra.ι R (F j) =
      UniversalEnvelopingAlgebra.ι R (F j) * UniversalEnvelopingAlgebra.ι R (E i)
        + (if i = j then UniversalEnvelopingAlgebra.ι R (H i) else 0) := by
  have h := iota_mul_sub (R := R) (E i) (F j)
  rw [hEF i j, sub_eq_iff_eq_add'] at h
  by_cases hij : i = j
  · rw [if_pos hij] at h
    rw [if_pos hij]
    exact h
  · rw [if_neg hij, map_zero] at h
    rw [if_neg hij]
    simpa using h

lemma triMon_mem (w v u : List κ) : triMon R H E F w v u ∈ triSpan R H E F :=
  Submodule.subset_span ⟨(w, v, u), rfl⟩

lemma Hword_mul_Eword_mem (v u : List κ) : Hword R H v * Eword R E u ∈ HEspan R H E :=
  Submodule.subset_span ⟨(v, u), rfl⟩

lemma Hword_mem_HwordSpan (v : List κ) : Hword R H v ∈ HwordSpan R H :=
  Submodule.subset_span ⟨v, rfl⟩

lemma Hword_mul_Eword_mem_triSpan (v u : List κ) :
    Hword R H v * Eword R E u ∈ triSpan R H E F := by
  have h : Hword R H v * Eword R E u = triMon R H E F [] v u := by simp [triMon]
  rw [h]
  exact triMon_mem R [] v u

/-- The span of the `H`-words is closed under left multiplication by an `H`-word. -/
lemma Hword_mul_HwordSpan (v : List κ) {r : UniversalEnvelopingAlgebra R L}
    (hr : r ∈ HwordSpan R H) : Hword R H v * r ∈ HwordSpan R H := by
  refine Submodule.span_induction (p := fun x _ => Hword R H v * x ∈ HwordSpan R H)
    ?_ ?_ ?_ ?_ hr
  · rintro x ⟨v', rfl⟩
    rw [← Hword_append]
    exact Hword_mem_HwordSpan R (v ++ v')
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of the `(H-word)*(E-word)` products is closed under left multiplication by an
`H`-word. -/
lemma Hword_mul_HEspan (v : List κ) {r : UniversalEnvelopingAlgebra R L}
    (hr : r ∈ HEspan R H E) : Hword R H v * r ∈ HEspan R H E := by
  refine Submodule.span_induction (p := fun x _ => Hword R H v * x ∈ HEspan R H E)
    ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    show Hword R H v * (Hword R H v' * Eword R E u') ∈ HEspan R H E
    rw [← mul_assoc, ← Hword_append]
    exact Hword_mul_Eword_mem R (v ++ v') u'
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of `(H-word)*(E-word)` products is closed under right multiplication by an
`E`-word. -/
lemma HEspan_mul_Eword (u : List κ) {r : UniversalEnvelopingAlgebra R L}
    (hr : r ∈ HEspan R H E) : r * Eword R E u ∈ HEspan R H E := by
  refine Submodule.span_induction (p := fun x _ => x * Eword R E u ∈ HEspan R H E)
    ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    show (Hword R H v' * Eword R E u') * Eword R E u ∈ HEspan R H E
    rw [mul_assoc, ← Eword_append]
    exact Hword_mul_Eword_mem R v' (u' ++ u)
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- Moving a single `eᵢ` past an `H`-word. -/
lemma Eimg_mul_Hword (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (v : List κ) (i : κ) :
    UniversalEnvelopingAlgebra.ι R (E i) * Hword R H v ∈ HEspan R H E := by
  induction v with
  | nil => simpa using Hword_mul_Eword_mem R [] [i]
  | cons j v' ih =>
      have hce : UniversalEnvelopingAlgebra.ι R (E i) * UniversalEnvelopingAlgebra.ι R (H j) =
          UniversalEnvelopingAlgebra.ι R (H j) * UniversalEnvelopingAlgebra.ι R (E i)
            - A j i • UniversalEnvelopingAlgebra.ι R (E i) := Eimg_mul_Himg R hHE i j
      have hstep : UniversalEnvelopingAlgebra.ι R (E i) * Hword R H (j :: v') =
          UniversalEnvelopingAlgebra.ι R (H j)
              * (UniversalEnvelopingAlgebra.ι R (E i) * Hword R H v')
            - A j i • (UniversalEnvelopingAlgebra.ι R (E i) * Hword R H v') := by
        rw [Hword_cons, ← mul_assoc, hce, sub_mul, smul_mul_assoc, mul_assoc]
      rw [hstep]
      exact Submodule.sub_mem _
        (by simpa using Hword_mul_HEspan R [j] ih)
        (Submodule.smul_mem _ _ ih)

/-- The span of `(H-word)*(E-word)` products is closed under left multiplication by a single
raising generator. -/
lemma Eimg_mul_HEspan (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (i : κ)
    {r : UniversalEnvelopingAlgebra R L} (hr : r ∈ HEspan R H E) :
    UniversalEnvelopingAlgebra.ι R (E i) * r ∈ HEspan R H E := by
  refine Submodule.span_induction
    (p := fun x _ => UniversalEnvelopingAlgebra.ι R (E i) * x ∈ HEspan R H E) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    show UniversalEnvelopingAlgebra.ι R (E i) * (Hword R H v' * Eword R E u') ∈ HEspan R H E
    rw [← mul_assoc]
    exact HEspan_mul_Eword R u' (Eimg_mul_Hword R hHE v' i)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of `(H-word)*(E-word)` products is closed under left multiplication by an
`E`-word. -/
lemma Eword_mul_HEspan (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (u : List κ)
    {r : UniversalEnvelopingAlgebra R L} (hr : r ∈ HEspan R H E) :
    Eword R E u * r ∈ HEspan R H E := by
  induction u with
  | nil => simpa using hr
  | cons k u' ih =>
      rw [Eword_cons, mul_assoc]
      exact Eimg_mul_HEspan R hHE k ih

/-- Moving an `E`-word past an `H`-word. -/
lemma Eword_mul_Hword (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (u v : List κ) :
    Eword R E u * Hword R H v ∈ HEspan R H E :=
  Eword_mul_HEspan R hHE u (by simpa using Hword_mul_Eword_mem R v [])

/-- Moving an `E`-word past a single `H`-generator. -/
lemma Eword_mul_Himg (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (u : List κ) (i : κ) :
    Eword R E u * UniversalEnvelopingAlgebra.ι R (H i) =
      UniversalEnvelopingAlgebra.ι R (H i) * Eword R E u
        - cartSum R A i u • Eword R E u := by
  induction u with
  | nil => simp [cartSum]
  | cons j u' ih =>
      have hstep : Eword R E (j :: u') * UniversalEnvelopingAlgebra.ι R (H i) =
          (UniversalEnvelopingAlgebra.ι R (E j) * UniversalEnvelopingAlgebra.ι R (H i))
              * Eword R E u'
            - (cartSum R A i u')
              • (UniversalEnvelopingAlgebra.ι R (E j) * Eword R E u') := by
        rw [Eword_cons, mul_assoc, ih, mul_sub, mul_smul_comm]
        simp only [mul_assoc]
      rw [hstep, Eimg_mul_Himg R hHE j i, cartSum_cons, Eword_cons, sub_mul, smul_mul_assoc,
        mul_assoc, add_smul]
      module

/-- Moving an `H`-word past a single lowering generator: the result is `fᵢ` times an element of
the span of the `H`-words. -/
lemma Hword_mul_Fimg (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j) • F j) (v : List κ) (i : κ) :
    ∃ R' ∈ HwordSpan R H,
      Hword R H v * UniversalEnvelopingAlgebra.ι R (F i)
        = UniversalEnvelopingAlgebra.ι R (F i) * R' := by
  induction v with
  | nil => exact ⟨1, Hword_mem_HwordSpan R [], by simp⟩
  | cons j v' ih =>
      obtain ⟨R', hR', hEq⟩ := ih
      refine ⟨UniversalEnvelopingAlgebra.ι R (H j) * R'
        - A j i • R', ?_, ?_⟩
      · exact Submodule.sub_mem _
          (by simpa using Hword_mul_HwordSpan R [j] hR')
          (Submodule.smul_mem _ _ hR')
      · calc Hword R H (j :: v') * UniversalEnvelopingAlgebra.ι R (F i)
            = UniversalEnvelopingAlgebra.ι R (H j)
                * (Hword R H v' * UniversalEnvelopingAlgebra.ι R (F i)) := by
              rw [Hword_cons, mul_assoc]
          _ = UniversalEnvelopingAlgebra.ι R (H j)
                * (UniversalEnvelopingAlgebra.ι R (F i) * R') := by rw [hEq]
          _ = (UniversalEnvelopingAlgebra.ι R (H j)
                * UniversalEnvelopingAlgebra.ι R (F i)) * R' := by rw [mul_assoc]
          _ = (UniversalEnvelopingAlgebra.ι R (F i) * UniversalEnvelopingAlgebra.ι R (H j)
                - A j i • UniversalEnvelopingAlgebra.ι R (F i)) * R' := by
              rw [Himg_mul_Fimg R hHF i j]
          _ = UniversalEnvelopingAlgebra.ι R (F i)
                * (UniversalEnvelopingAlgebra.ι R (H j) * R')
              - A j i • (UniversalEnvelopingAlgebra.ι R (F i) * R') := by
              rw [sub_mul, smul_mul_assoc, mul_assoc]
          _ = UniversalEnvelopingAlgebra.ι R (F i)
                * (UniversalEnvelopingAlgebra.ι R (H j) * R' - A j i • R') := by
              rw [mul_sub, mul_smul_comm]

/-- Moving an `E`-word past a single lowering generator: the result is `fᵢ` times the `E`-word
plus a correction in the span of the `(H-word)*(E-word)` products. -/
lemma Eword_mul_Fimg (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0) (u : List κ) (i : κ) :
    ∃ S ∈ HEspan R H E,
      Eword R E u * UniversalEnvelopingAlgebra.ι R (F i)
        = UniversalEnvelopingAlgebra.ι R (F i) * Eword R E u + S := by
  induction u with
  | nil => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | cons k u' ih =>
      obtain ⟨S', hS', hEq⟩ := ih
      refine ⟨(if k = i then UniversalEnvelopingAlgebra.ι R (H k) * Eword R E u' else 0)
        + UniversalEnvelopingAlgebra.ι R (E k) * S', ?_, ?_⟩
      · refine Submodule.add_mem _ ?_ (Eimg_mul_HEspan R hHE k hS')
        by_cases hk : k = i
        · subst hk
          rw [if_pos rfl]
          simpa using Hword_mul_Eword_mem R [k] u'
        · rw [if_neg hk]
          exact Submodule.zero_mem _
      · have hA : Eword R E (k :: u') * UniversalEnvelopingAlgebra.ι R (F i)
            = (UniversalEnvelopingAlgebra.ι R (E k)
                  * UniversalEnvelopingAlgebra.ι R (F i)) * Eword R E u'
              + UniversalEnvelopingAlgebra.ι R (E k) * S' := by
          rw [Eword_cons, mul_assoc, hEq, mul_add]
          simp only [mul_assoc]
        have hB : (UniversalEnvelopingAlgebra.ι R (E k)
              * UniversalEnvelopingAlgebra.ι R (F i)) * Eword R E u'
            + UniversalEnvelopingAlgebra.ι R (E k) * S'
            = UniversalEnvelopingAlgebra.ι R (F i)
                * (UniversalEnvelopingAlgebra.ι R (E k) * Eword R E u')
              + ((if k = i then UniversalEnvelopingAlgebra.ι R (H k) * Eword R E u' else 0)
                + UniversalEnvelopingAlgebra.ι R (E k) * S') := by
          rw [Eimg_mul_Fimg R hEF k i, add_mul]
          by_cases hk : k = i
          · subst hk
            rw [if_pos rfl, if_pos rfl]
            simp only [mul_assoc]
            abel
          · rw [if_neg hk, if_neg hk]
            simp only [mul_assoc, zero_mul, zero_add]
            abel
        have hstep : Eword R E (k :: u') * UniversalEnvelopingAlgebra.ι R (F i)
            = UniversalEnvelopingAlgebra.ι R (F i)
                * (UniversalEnvelopingAlgebra.ι R (E k) * Eword R E u')
              + ((if k = i then UniversalEnvelopingAlgebra.ι R (H k) * Eword R E u' else 0)
                + UniversalEnvelopingAlgebra.ι R (E k) * S') := hA.trans hB
        rw [hstep, ← Eword_cons]

/-- `Fw w * r * Eu u ∈ T` for `r` in the span of the `H`-words. -/
lemma triSpan_mem_of_HwordSpan (w u : List κ) {r : UniversalEnvelopingAlgebra R L}
    (hr : r ∈ HwordSpan R H) : Fword R F w * r * Eword R E u ∈ triSpan R H E F := by
  refine Submodule.span_induction
    (p := fun x _ => Fword R F w * x * Eword R E u ∈ triSpan R H E F) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨v', rfl⟩
    have h : Fword R F w * Hword R H v' * Eword R E u = triMon R H E F w v' u := by
      simp only [triMon]
    rw [h]
    exact triMon_mem R w v' u
  · simp
  · intro x y _ _ hx hy
    rw [mul_add, add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- `Fw w * Hw v * r ∈ T` for `r` in the span of the `(H-word)*(E-word)` products. -/
lemma triSpan_mem_of_HEspan (w v : List κ) {r : UniversalEnvelopingAlgebra R L}
    (hr : r ∈ HEspan R H E) : Fword R F w * Hword R H v * r ∈ triSpan R H E F := by
  refine Submodule.span_induction
    (p := fun x _ => Fword R F w * Hword R H v * x ∈ triSpan R H E F) ?_ ?_ ?_ ?_ hr
  · rintro x ⟨⟨v', u'⟩, rfl⟩
    have h : Fword R F w * Hword R H v * (Hword R H v' * Eword R E u')
        = triMon R H E F w (v ++ v') u' := by
      simp only [triMon, Hword_append, mul_assoc]
    rw [h]
    exact triMon_mem R w (v ++ v') u'
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The span of the triangular monomials is closed under right multiplication by `eᵢ`. -/
lemma triSpan_mul_Eimg (i : κ) {t : UniversalEnvelopingAlgebra R L}
    (ht : t ∈ triSpan R H E F) :
    t * UniversalEnvelopingAlgebra.ι R (E i) ∈ triSpan R H E F := by
  refine Submodule.span_induction
    (p := fun x _ => x * UniversalEnvelopingAlgebra.ι R (E i) ∈ triSpan R H E F) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨⟨w, v, u⟩, rfl⟩
    have h : triMon R H E F w v u * UniversalEnvelopingAlgebra.ι R (E i)
        = triMon R H E F w v (u ++ [i]) := by
      simp only [triMon, Eword_append, Eword_singleton, mul_assoc]
    rw [h]
    exact triMon_mem R w v (u ++ [i])
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The span of the triangular monomials is closed under right multiplication by `hᵢ`. -/
lemma triSpan_mul_Himg (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j) (i : κ)
    {t : UniversalEnvelopingAlgebra R L} (ht : t ∈ triSpan R H E F) :
    t * UniversalEnvelopingAlgebra.ι R (H i) ∈ triSpan R H E F := by
  refine Submodule.span_induction
    (p := fun x _ => x * UniversalEnvelopingAlgebra.ι R (H i) ∈ triSpan R H E F) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨⟨w, v, u⟩, rfl⟩
    have h1 : Fword R F w * Hword R H v
          * (Eword R E u * UniversalEnvelopingAlgebra.ι R (H i))
        = Fword R F w * Hword R H v
            * (UniversalEnvelopingAlgebra.ι R (H i) * Eword R E u)
          - (cartSum R A i u) • (Fword R F w * Hword R H v * Eword R E u) := by
      rw [Eword_mul_Himg R hHE u i, mul_sub, mul_smul_comm]
    have h2 : Fword R F w * Hword R H v
          * (UniversalEnvelopingAlgebra.ι R (H i) * Eword R E u)
        = triMon R H E F w (v ++ [i]) u := by
      simp only [triMon, Hword_append, Hword_singleton, mul_assoc]
    have h3 : Fword R F w * Hword R H v * Eword R E u = triMon R H E F w v u := by
      simp only [triMon]
    have key : triMon R H E F w v u * UniversalEnvelopingAlgebra.ι R (H i)
        = triMon R H E F w (v ++ [i]) u - (cartSum R A i u) • triMon R H E F w v u := by
      rw [triMon, mul_assoc, h1, h2, h3]
    rw [key]
    exact Submodule.sub_mem _ (triMon_mem R w (v ++ [i]) u)
      (Submodule.smul_mem _ _ (triMon_mem R w v u))
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The span of the triangular monomials is closed under right multiplication by `fᵢ`. -/
lemma triSpan_mul_Fimg (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j) • F j)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0) (i : κ)
    {t : UniversalEnvelopingAlgebra R L} (ht : t ∈ triSpan R H E F) :
    t * UniversalEnvelopingAlgebra.ι R (F i) ∈ triSpan R H E F := by
  refine Submodule.span_induction
    (p := fun x _ => x * UniversalEnvelopingAlgebra.ι R (F i) ∈ triSpan R H E F) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨⟨w, v, u⟩, rfl⟩
    obtain ⟨S, hS, hEq⟩ := Eword_mul_Fimg R hHE hEF u i
    obtain ⟨Rv, hRv, hEqv⟩ := Hword_mul_Fimg R hHF v i
    have key : triMon R H E F w v u * UniversalEnvelopingAlgebra.ι R (F i)
        = Fword R F (w ++ [i]) * Rv * Eword R E u + Fword R F w * Hword R H v * S := by
      rw [triMon]
      calc Fword R F w * Hword R H v * Eword R E u * UniversalEnvelopingAlgebra.ι R (F i)
          = Fword R F w
              * (Hword R H v
                * (Eword R E u * UniversalEnvelopingAlgebra.ι R (F i))) := by
            simp only [mul_assoc]
        _ = Fword R F w
              * (Hword R H v
                * (UniversalEnvelopingAlgebra.ι R (F i) * Eword R E u + S)) := by rw [hEq]
        _ = Fword R F w
              * (Hword R H v * (UniversalEnvelopingAlgebra.ι R (F i) * Eword R E u))
            + Fword R F w * (Hword R H v * S) := by simp only [mul_add]
        _ = Fword R F w
              * ((Hword R H v * UniversalEnvelopingAlgebra.ι R (F i)) * Eword R E u)
            + Fword R F w * (Hword R H v * S) := by simp only [mul_assoc]
        _ = Fword R F w
              * ((UniversalEnvelopingAlgebra.ι R (F i) * Rv) * Eword R E u)
            + Fword R F w * (Hword R H v * S) := by rw [hEqv]
        _ = Fword R F (w ++ [i]) * Rv * Eword R E u + Fword R F w * Hword R H v * S := by
            rw [Fword_append, Fword_singleton]
            simp only [mul_assoc]
    rw [key]
    exact Submodule.add_mem _ (triSpan_mem_of_HwordSpan R (w ++ [i]) u hRv)
      (triSpan_mem_of_HEspan R w v hS)
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The subalgebra of `U(L)` consisting of the elements acting on the span `T` of the triangular
monomials by right multiplication preserving `T`. -/
def TRight (H E F : κ → L) : Subalgebra R (UniversalEnvelopingAlgebra R L) where
  carrier := {u | ∀ x ∈ triSpan R H E F, x * u ∈ triSpan R H E F}
  zero_mem' := by intro x _; rw [mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb x hx
    rw [mul_add]
    exact Submodule.add_mem _ (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    have h1 : x * a ∈ triSpan R H E F := ha x hx
    have h2 : x * a * b ∈ triSpan R H E F := hb (x * a) h1
    rwa [mul_assoc] at h2
  one_mem' := by intro x hx; simpa using hx
  algebraMap_mem' := by
    intro c x hx
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
    exact Submodule.smul_mem _ c hx

lemma mem_TRight (u : UniversalEnvelopingAlgebra R L) :
    u ∈ TRight R H E F ↔ ∀ x ∈ triSpan R H E F, x * u ∈ triSpan R H E F := Iff.rfl

/-- Every element of `ι(L)` lies in the subalgebra of right-preservers of `T`: the three
families of generators do, and those generate `L` as a Lie algebra. -/
lemma iota_mem_TRight
    (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j) • F j)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0)
    (hgen : LieSubalgebra.lieSpan R L (Set.range H ∪ Set.range E ∪ Set.range F) = ⊤)
    (x : L) : UniversalEnvelopingAlgebra.ι R x ∈ TRight R H E F := by
  let N : LieSubalgebra R L :=
    { carrier := {x : L | UniversalEnvelopingAlgebra.ι R x ∈ TRight R H E F}
      zero_mem' := by
        change UniversalEnvelopingAlgebra.ι R (0 : L) ∈ TRight R H E F
        rw [map_zero]
        exact (TRight R H E F).zero_mem
      add_mem' := by
        intro p q hp hq
        change UniversalEnvelopingAlgebra.ι R (p + q) ∈ TRight R H E F
        rw [map_add]
        exact (TRight R H E F).add_mem hp hq
      smul_mem' := by
        intro c p hp
        change UniversalEnvelopingAlgebra.ι R (c • p) ∈ TRight R H E F
        rw [map_smul]
        exact (TRight R H E F).toSubmodule.smul_mem c hp
      lie_mem' := by
        intro p q hp hq
        change UniversalEnvelopingAlgebra.ι R ⁅p, q⁆ ∈ TRight R H E F
        rw [LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) p q,
          LieRing.of_associative_ring_bracket]
        exact (TRight R H E F).sub_mem ((TRight R H E F).mul_mem hp hq)
          ((TRight R H E F).mul_mem hq hp) }
  have hle : LieSubalgebra.lieSpan R L (Set.range H ∪ Set.range E ∪ Set.range F) ≤ N := by
    refine LieSubalgebra.lieSpan_le.mpr ?_
    intro y hy
    rcases hy with (hy | hy) | hy
    · obtain ⟨i, rfl⟩ := hy
      exact (mem_TRight R (UniversalEnvelopingAlgebra.ι R (H i))).mpr
        (fun t ht => triSpan_mul_Himg R hHE i ht)
    · obtain ⟨i, rfl⟩ := hy
      exact (mem_TRight R (UniversalEnvelopingAlgebra.ι R (E i))).mpr
        (fun t ht => triSpan_mul_Eimg R i ht)
    · obtain ⟨i, rfl⟩ := hy
      exact (mem_TRight R (UniversalEnvelopingAlgebra.ι R (F i))).mpr
        (fun t ht => triSpan_mul_Fimg R hHE hHF hEF i ht)
  have hx : x ∈ LieSubalgebra.lieSpan R L (Set.range H ∪ Set.range E ∪ Set.range F) := by
    rw [hgen]
    trivial
  exact hle hx

end Main

/-- **Triangular spanning.**  If the three families `H`, `E`, `F` generate the Lie algebra `L`
and satisfy the triangular commutation relations with structure constants `A`, then every
element of the universal enveloping algebra `U(L)` is an `R`-linear combination of triangular
monomials `(F-word) * (H-word) * (E-word)`. -/
theorem span_triMon_eq_top {R L : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] {ι : Type*} [DecidableEq ι] (A : ι → ι → R) (H E F : ι → L)
    (hgen : LieSubalgebra.lieSpan R L (Set.range H ∪ Set.range E ∪ Set.range F) = ⊤)
    (hHH : ∀ i j, ⁅H i, H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j) • F j)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0) :
    Submodule.span R (Set.range (fun p : List ι × List ι × List ι =>
      ((p.1.map (fun i => UniversalEnvelopingAlgebra.ι R (F i))).prod) *
      ((p.2.1.map (fun i => UniversalEnvelopingAlgebra.ι R (H i))).prod) *
      ((p.2.2.map (fun i => UniversalEnvelopingAlgebra.ι R (E i))).prod))) = ⊤ := by
  show triSpan R H E F = ⊤
  have hle : (⊤ : Subalgebra R (UniversalEnvelopingAlgebra R L)) ≤ TRight R H E F := by
    rw [← Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]
    exact Algebra.adjoin_le (fun y hy => by
      obtain ⟨z, rfl⟩ := hy
      exact iota_mem_TRight R hHE hHF hEF hgen z)
  rw [eq_top_iff]
  intro u _
  have h1 : (1 : UniversalEnvelopingAlgebra R L) ∈ triSpan R H E F := by
    have h : triMon R H E F ([] : List ι) [] [] ∈ triSpan R H E F :=
      triMon_mem (R := R) (H := H) (E := E) (F := F) ([] : List ι) [] []
    have h0 : triMon R H E F ([] : List ι) [] [] = 1 := by simp [triMon]
    rwa [h0] at h
  have hmem : u ∈ TRight R H E F :=
    hle (show u ∈ (⊤ : Subalgebra R (UniversalEnvelopingAlgebra R L)) from trivial)
  have h2 : ∀ x ∈ triSpan R H E F, x * u ∈ triSpan R H E F := (mem_TRight R u).mp hmem
  simpa using h2 1 h1

end Commons.Algebra.Lie.TriangularSpan
