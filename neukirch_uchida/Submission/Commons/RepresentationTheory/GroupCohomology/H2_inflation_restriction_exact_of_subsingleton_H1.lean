import Mathlib.Combinatorics.Quiver.ReflQuiver
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.descent_to_quotient_of_invariant

/-!
# Exactness of the inflation–restriction sequence in degree 2

Let `S ◁ G` be a normal subgroup of a group `G`, `k` a commutative ring and `A` a `k`-linear
`G`-representation.  The purpose of this file is the following statement: if `H¹(S, A) = 0`, then
the sequence
`H²(G ⧸ S, A^S) --inf--> H²(G, A) --res--> H²(S, A)`
is exact at `H²(G, A)`, i.e. the range of the inflation map is the kernel of the restriction map.

The proof is a direct computation on the level of cocycles.  Given a `2`-cocycle `y` of `G` with
values in `A` whose restriction to `S` is a coboundary (this is what `res [y] = 0` means), one
first corrects `y` by a coboundary so that it vanishes on `S × S`.  The failure of such a `y` to be
right `S`-invariant in its first variable is measured by the `1`-cocycles
`θ_h : s ↦ y (s,h) - y (h, h⁻¹ s h)` on `S`; as `H¹(S,A) = 0`, each `θ_h` is a coboundary, and
choosing primitives `α_h` allows us to build a `1`-cochain `u` on `G` with
`u (g s) - u g = - y (g, s)` and `ρ(s) (u h) - u (s h) = y (s, h)` for all `s ∈ S`.  Then
`z := y - d u` vanishes on `(G × S) ∪ (S × G)`, and the cocycle identity shows that `z` is
invariant under `S` in both variables and takes values in `A^S`, so that `z` descends to a
`2`-cocycle of `G ⧸ S` with values in `A^S` whose inflation is `y`.

## Main results

* `Commons.RepresentationTheory.GroupCohomology.exists_cocycle_quotient_of_vanishing`: the
  cocycle-level statement used above.
* `Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1`:
  the headline statement, for `ℤ`-representations.
-/

open CategoryTheory Representation

namespace Commons.RepresentationTheory.GroupCohomology

open groupCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G]

/-- A 2-cocycle `y` of `G` with values in `A` satisfies the "cocycle identity twisted along `S`":
if `y` vanishes on `S × S`, then `y (g, s t) - y (g,s) = y (g s, t)` for `g : G`, `s t : S`. -/
lemma cocycles₂_sub_eq_of_mem {A : Rep k G} {S : Subgroup G} (y : cocycles₂ A)
    (hy : ∀ s t : S, y (s.1, t.1) = 0) (g : G) (s t : S) :
    y (g, s.1 * t.1) - y (g, s.1) = y (g * s.1, t.1) := by
  have h := (mem_cocycles₂_iff y).1 y.2 g s.1 t.1
  rw [hy s t, map_zero, zero_add] at h
  rw [← h]; abel

lemma cocycles₂_sub_eq_of_mem' {A : Rep k G} {S : Subgroup G} (y : cocycles₂ A)
    (hy : ∀ s t : S, y (s.1, t.1) = 0) (g : G) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    y (g, s * t) - y (g, s) = y (g * s, t) :=
  cocycles₂_sub_eq_of_mem y hy g ⟨s, hs⟩ ⟨t, ht⟩

/-- The 1-cocycle of `S` measuring the failure of `y` to be right-`S`-invariant in its first
variable: `s ↦ y (s, h) - y (h, h⁻¹ s h)`. -/
noncomputable def thetaOfCocycle {A : Rep k G} (S : Subgroup G) (y : cocycles₂ A) (h : G) : S → A :=
  fun s => y (s.1, h) - y (h, h⁻¹ * s.1 * h)

lemma thetaOfCocycle_mem_cocycles₁ {A : Rep k G} (S : Subgroup G) [S.Normal] (y : cocycles₂ A)
    (hy : ∀ s t : S, y (s.1, t.1) = 0) (h : G) :
    thetaOfCocycle S y h ∈ cocycles₁ (Rep.res S.subtype A) := by
  rw [mem_cocycles₁_iff]
  intro s t
  show y ((s * t).1, h) - y (h, h⁻¹ * (s * t).1 * h)
    = A.ρ s.1 (y (t.1, h) - y (h, h⁻¹ * t.1 * h)) + (y (s.1, h) - y (h, h⁻¹ * s.1 * h))
  have hst : ((s * t : S) : G) = s.1 * t.1 := rfl
  rw [hst]
  have h1 : y (s.1 * t.1, h) = A.ρ s.1 (y (t.1, h)) + y (s.1, t.1 * h) := by
    have hh := (mem_cocycles₂_iff y).1 y.2 s.1 t.1 h
    rw [hy s t, add_zero] at hh
    exact hh
  have h2 : A.ρ s.1 (y (h, h⁻¹ * t.1 * h))
      = y (s.1 * h, h⁻¹ * t.1 * h) + y (s.1, h) - y (s.1, t.1 * h) := by
    have hh := (mem_cocycles₂_iff y).1 y.2 s.1 h (h⁻¹ * t.1 * h)
    have hh2 : h * (h⁻¹ * t.1 * h) = t.1 * h := by group
    rw [hh2] at hh
    rw [eq_sub_iff_add_eq, eq_comm]
    exact hh
  have h3 : y (s.1 * h, h⁻¹ * t.1 * h)
      = y (h, h⁻¹ * (s.1 * t.1) * h) - y (h, h⁻¹ * s.1 * h) := by
    have hh := cocycles₂_sub_eq_of_mem y hy h
      ⟨h⁻¹ * s.1 * h, Subgroup.Normal.conj_mem' ‹S.Normal› s.1 s.2 h⟩
      ⟨h⁻¹ * t.1 * h, Subgroup.Normal.conj_mem' ‹S.Normal› t.1 t.2 h⟩
    have e1 : h * (h⁻¹ * s.1 * h) = s.1 * h := by group
    have e2 : (h⁻¹ * s.1 * h) * (h⁻¹ * t.1 * h) = h⁻¹ * (s.1 * t.1) * h := by group
    rw [e1, e2] at hh
    rw [hh]
  rw [h1, map_sub, h2, h3]
  abel

variable {A : Rep k G} (S : Subgroup G) [S.Normal] (y : cocycles₂ A)
  (hy : ∀ s t : S, y (s.1, t.1) = 0)

/-- A choice, for each `h : G`, of an element `α` of `A` with `ρ(s) α - α = θ_h(s)`, where
`θ_h` is the 1-cocycle `s ↦ y (s,h) - y (h, h⁻¹ s h)`.  It exists because `H¹(S,A) = 0`. -/
noncomputable def alphaOfCocycle (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (h : G) : A :=
  Classical.choose (exists_sub_eq_of_subsingleton_H1 S A hsub (thetaOfCocycle S y h)
    (thetaOfCocycle_mem_cocycles₁ S y hy h))

lemma alphaOfCocycle_spec (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (h : G) (s : S) :
    A.ρ s.1 (alphaOfCocycle S y hy hsub h) - alphaOfCocycle S y hy hsub h
      = thetaOfCocycle S y h s :=
  Classical.choose_spec (exists_sub_eq_of_subsingleton_H1 S A hsub (thetaOfCocycle S y h)
    (thetaOfCocycle_mem_cocycles₁ S y hy h)) s

/-- A set-theoretic section of the quotient map `G → G ⧸ S`. -/
noncomputable def secQuot (g : G) : G := Quotient.out (QuotientGroup.mk' S g)

lemma mk'_secQuot (g : G) : QuotientGroup.mk' S (secQuot S g) = QuotientGroup.mk' S g := by
  rw [secQuot]
  exact QuotientGroup.out_eq' (QuotientGroup.mk' S g)

lemma secQuot_congr {g g' : G} (h : QuotientGroup.mk' S g = QuotientGroup.mk' S g') :
    secQuot S g = secQuot S g' := by
  simp only [secQuot, h]

lemma inv_mul_secQuot_mem (g : G) : (secQuot S g)⁻¹ * g ∈ S :=
  (QuotientGroup.eq).1 (mk'_secQuot S g)

lemma secQuot_one_mem : secQuot S (1 : G) ∈ S := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, mk'_secQuot, QuotientGroup.mk'_apply]
  exact QuotientGroup.mk_one S

/-- The "primitive" of the cocycle `y`, chosen so that `u (g s) - u g = - y (g,s)` for `s ∈ S`
and `ρ(s) (u h) - u (s h) = y (s,h)`. -/
noncomputable def uOfCocycle (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g : G) : A :=
  alphaOfCocycle S y hy hsub (secQuot S g)
    - y (secQuot S g, (secQuot S g)⁻¹ * g)
    - alphaOfCocycle S y hy hsub (secQuot S (1 : G))

lemma uOfCocycle_sub (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g : G) (s : S) : uOfCocycle S y hy hsub (g * s.1) = uOfCocycle S y hy hsub g - y (g, s.1) := by
  have hs : (QuotientGroup.mk' S s.1 : G ⧸ S) = 1 := (QuotientGroup.eq_one_iff s.1).2 s.2
  have hq : QuotientGroup.mk' S (g * s.1) = QuotientGroup.mk' S g := by rw [map_mul, hs, mul_one]
  have hsec : secQuot S (g * s.1) = secQuot S g := secQuot_congr S hq
  have hF2 : y (secQuot S g, ((secQuot S g)⁻¹ * g) * s.1) - y (secQuot S g, (secQuot S g)⁻¹ * g)
      = y (g, s.1) := by
    have hh := cocycles₂_sub_eq_of_mem' y hy (secQuot S g) (inv_mul_secQuot_mem S g) s.2
    rwa [show secQuot S g * ((secQuot S g)⁻¹ * g) = g from by group] at hh
  have hu : uOfCocycle S y hy hsub (g * s.1)
      = alphaOfCocycle S y hy hsub (secQuot S g)
        - y (secQuot S g, ((secQuot S g)⁻¹ * g) * s.1)
        - alphaOfCocycle S y hy hsub (secQuot S (1 : G)) := by
    simp only [uOfCocycle, hsec]
    rw [show (secQuot S g)⁻¹ * (g * s.1) = ((secQuot S g)⁻¹ * g) * s.1 from by group]
  rw [hu]
  simp only [uOfCocycle]
  rw [← hF2]
  abel

lemma alphaOfCocycle_secQuot_one_mem_invariants
    (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) (s : S) :
    A.ρ s.1 (alphaOfCocycle S y hy hsub (secQuot S (1 : G)))
      = alphaOfCocycle S y hy hsub (secQuot S (1 : G)) := by
  have hspec := alphaOfCocycle_spec S y hy hsub (secQuot S (1 : G)) s
  rw [thetaOfCocycle] at hspec
  have h1 : y (s.1, secQuot S (1 : G)) = 0 := hy s ⟨secQuot S (1 : G), secQuot_one_mem S⟩
  have h2 : y (secQuot S (1 : G), (secQuot S (1 : G))⁻¹ * s.1 * secQuot S (1 : G)) = 0 :=
    hy ⟨secQuot S (1 : G), secQuot_one_mem S⟩
      ⟨(secQuot S (1 : G))⁻¹ * s.1 * secQuot S (1 : G),
        Subgroup.Normal.conj_mem' ‹S.Normal› s.1 s.2 (secQuot S (1 : G))⟩
  rw [h1, h2, sub_zero] at hspec
  exact sub_eq_zero.1 hspec

lemma uOfCocycle_one (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    uOfCocycle S y hy hsub (1 : G) = 0 := by
  have h1 : y (secQuot S (1 : G), (secQuot S (1 : G))⁻¹) = 0 := by
    simpa using hy ⟨secQuot S (1 : G), secQuot_one_mem S⟩
      ⟨(secQuot S (1 : G))⁻¹, S.inv_mem (secQuot_one_mem S)⟩
  simp only [uOfCocycle, mul_one]
  rw [h1]
  abel

set_option maxHeartbeats 800000 in
lemma uOfCocycle_rho_sub (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (s : S) (h : G) :
    A.ρ s.1 (uOfCocycle S y hy hsub h) - uOfCocycle S y hy hsub (s.1 * h) = y (s.1, h) := by
  have hs : (QuotientGroup.mk' S s.1 : G ⧸ S) = 1 := (QuotientGroup.eq_one_iff s.1).2 s.2
  have hq : QuotientGroup.mk' S (s.1 * h) = QuotientGroup.mk' S h := by rw [map_mul, hs, one_mul]
  have hsec : secQuot S (s.1 * h) = secQuot S h := secQuot_congr S hq
  have hs0 : (secQuot S h)⁻¹ * h ∈ S := inv_mul_secQuot_mem S h
  have hs1 : (secQuot S h)⁻¹ * s.1 * secQuot S h ∈ S :=
    Subgroup.Normal.conj_mem' ‹S.Normal› s.1 s.2 (secQuot S h)
  have hF2 : y (secQuot S h, ((secQuot S h)⁻¹ * s.1 * secQuot S h) * ((secQuot S h)⁻¹ * h))
      - y (secQuot S h, (secQuot S h)⁻¹ * s.1 * secQuot S h)
      = y (s.1 * secQuot S h, (secQuot S h)⁻¹ * h) := by
    have hh := cocycles₂_sub_eq_of_mem' y hy (secQuot S h) hs1 hs0
    rwa [show secQuot S h * ((secQuot S h)⁻¹ * s.1 * secQuot S h) = s.1 * secQuot S h from by
      group] at hh
  have halpha : A.ρ s.1 (alphaOfCocycle S y hy hsub (secQuot S h))
      - alphaOfCocycle S y hy hsub (secQuot S h)
      = y (s.1, secQuot S h) - y (secQuot S h, (secQuot S h)⁻¹ * s.1 * secQuot S h) := by
    have hspec := alphaOfCocycle_spec S y hy hsub (secQuot S h) s
    rw [thetaOfCocycle] at hspec
    exact hspec
  have hc := alphaOfCocycle_secQuot_one_mem_invariants S y hy hsub s
  have hcy := (mem_cocycles₂_iff y).1 y.2 s.1 (secQuot S h) ((secQuot S h)⁻¹ * h)
  rw [show secQuot S h * ((secQuot S h)⁻¹ * h) = h from by group] at hcy
  have hkey : y (secQuot S h, (secQuot S h)⁻¹ * (s.1 * h))
      = y (s.1 * secQuot S h, (secQuot S h)⁻¹ * h)
        + y (secQuot S h, (secQuot S h)⁻¹ * s.1 * secQuot S h) := by
    rw [show (secQuot S h)⁻¹ * (s.1 * h)
        = ((secQuot S h)⁻¹ * s.1 * secQuot S h) * ((secQuot S h)⁻¹ * h) from by group]
    rw [← hF2]; abel
  have hkey2 : y (s.1 * secQuot S h, (secQuot S h)⁻¹ * h)
      = A.ρ s.1 (y (secQuot S h, (secQuot S h)⁻¹ * h)) + y (s.1, h) - y (s.1, secQuot S h) := by
    rw [eq_sub_iff_add_eq, ← hcy]
  have expand : A.ρ s.1 (uOfCocycle S y hy hsub h) - uOfCocycle S y hy hsub (s.1 * h)
      = (A.ρ s.1 (alphaOfCocycle S y hy hsub (secQuot S h))
            - alphaOfCocycle S y hy hsub (secQuot S h))
        - A.ρ s.1 (y (secQuot S h, (secQuot S h)⁻¹ * h))
        + y (secQuot S h, (secQuot S h)⁻¹ * (s.1 * h))
        + (alphaOfCocycle S y hy hsub (secQuot S (1 : G))
            - A.ρ s.1 (alphaOfCocycle S y hy hsub (secQuot S (1 : G)))) := by
    simp only [uOfCocycle, hsec]
    rw [map_sub, map_sub]
    abel
  rw [expand, halpha, hc, sub_self, add_zero, hkey, hkey2]
  abel

lemma uOfCocycle_mem_S (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) (s : S) :
    uOfCocycle S y hy hsub s.1 = 0 := by
  have hy1 : y (1, s.1) = 0 := by simpa using hy (1 : S) s
  have h := uOfCocycle_sub S y hy hsub (1 : G) s
  rw [one_mul, uOfCocycle_one S y hy hsub, hy1, sub_zero] at h
  exact h

/-- The corrected `2`-cochain `z = y - d u`; by construction it vanishes on `(G × S) ∪ (S × G)`. -/
noncomputable def zOfCocycle (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    G × G → A :=
  fun p => y p - (d₁₂ A).hom (uOfCocycle S y hy hsub) p

lemma zOfCocycle_mem_cocycles₂ (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    zOfCocycle S y hy hsub ∈ cocycles₂ A := by
  have h1 : (fun p : G × G => (d₁₂ A).hom (uOfCocycle S y hy hsub) p) ∈ cocycles₂ A :=
    d₁₂_apply_mem_cocycles₂ (uOfCocycle S y hy hsub)
  have h2 : (fun p : G × G => y p) ∈ cocycles₂ A := y.2
  have h := sub_mem h2 h1
  convert h using 1
  ext p
  rfl

lemma zOfCocycle_fst_mem (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g : G) (s : S) : zOfCocycle S y hy hsub (g, s.1) = 0 := by
  have h1 := uOfCocycle_sub S y hy hsub g s
  have h2 := uOfCocycle_mem_S S y hy hsub s
  simp only [zOfCocycle, d₁₂_hom_apply]
  rw [h1, h2, map_zero]
  abel

lemma zOfCocycle_snd_mem (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (s : S) (h : G) : zOfCocycle S y hy hsub (s.1, h) = 0 := by
  have h1 := uOfCocycle_rho_sub S y hy hsub s h
  have h2 := uOfCocycle_mem_S S y hy hsub s
  simp only [zOfCocycle, d₁₂_hom_apply]
  rw [h2, add_zero, h1, sub_self]

lemma zOfCocycle_snd_mul (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g h : G) (s : S) : zOfCocycle S y hy hsub (g, h * s.1) = zOfCocycle S y hy hsub (g, h) := by
  have hz := (mem_cocycles₂_def (zOfCocycle S y hy hsub)).1 (zOfCocycle_mem_cocycles₂ S y hy hsub)
    g h s.1
  rw [zOfCocycle_fst_mem S y hy hsub (g * h) s, zOfCocycle_fst_mem S y hy hsub h s,
    map_zero] at hz
  simpa [sub_eq_zero] using hz

lemma zOfCocycle_snd_mul' (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g : G) (s : S) (h : G) : zOfCocycle S y hy hsub (g, s.1 * h) = zOfCocycle S y hy hsub (g, h) := by
  have hsh : s.1 * h = h * (h⁻¹ * s.1 * h) := by group
  rw [hsh]
  exact zOfCocycle_snd_mul S y hy hsub g h ⟨h⁻¹ * s.1 * h,
    Subgroup.Normal.conj_mem' ‹S.Normal› s.1 s.2 h⟩

lemma zOfCocycle_fst_mul (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g h : G) (s : S) : zOfCocycle S y hy hsub (g * s.1, h) = zOfCocycle S y hy hsub (g, h) := by
  have hz := (mem_cocycles₂_def (zOfCocycle S y hy hsub)).1 (zOfCocycle_mem_cocycles₂ S y hy hsub)
    g s.1 h
  rw [zOfCocycle_snd_mem S y hy hsub s h, zOfCocycle_fst_mem S y hy hsub g s, map_zero] at hz
  rw [zOfCocycle_snd_mul' S y hy hsub g s h] at hz
  rw [zero_sub, sub_zero, neg_add_eq_zero] at hz
  exact hz

lemma zOfCocycle_invariants (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (g h : G) (s : S) : A.ρ s.1 (zOfCocycle S y hy hsub (g, h)) = zOfCocycle S y hy hsub (g, h) := by
  have hz := (mem_cocycles₂_def (zOfCocycle S y hy hsub)).1 (zOfCocycle_mem_cocycles₂ S y hy hsub)
    s.1 g h
  rw [zOfCocycle_snd_mem S y hy hsub s (g * h), zOfCocycle_snd_mem S y hy hsub s g, sub_zero,
    add_zero] at hz
  have hsg : s.1 * g = g * (g⁻¹ * s.1 * g) := by group
  rw [hsg, zOfCocycle_fst_mul S y hy hsub g h ⟨g⁻¹ * s.1 * g,
    Subgroup.Normal.conj_mem' ‹S.Normal› s.1 s.2 g⟩] at hz
  simpa [sub_eq_zero] using hz

/-- The action of `G ⧸ S` on the invariants `A^S` is given by the action of any representative. -/
lemma quotientToInvariants_rho_apply (g : G) (x : (Rep.res S.subtype A).ρ.invariants) :
    (((A.ρ.quotientToInvariants S) (QuotientGroup.mk' S g)) x : A) = A.ρ g (x : A) := by
  simp [Representation.quotientToInvariants, Representation.ofQuotient_coe_apply]

set_option maxHeartbeats 800000 in
/-- **The cocycle-level statement.**  Let `y` be a `2`-cocycle of `G` with values in `A` which
vanishes on `S × S`.  If `H¹(S,A) = 0`, then `y` is cohomologous to the inflation of a `2`-cocycle
of `G ⧸ S` with values in the invariants `A^S`. -/
lemma exists_cocycle_quotient_of_vanishing
    (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    ∃ x : cocycles₂ (A.quotientToInvariants S),
      ∀ g h : G, (x (QuotientGroup.mk' S g, QuotientGroup.mk' S h) : A)
        = zOfCocycle S y hy hsub (g, h) := by
  obtain ⟨Z, hZ⟩ := descent_to_quotient_of_invariant S A (zOfCocycle S y hy hsub)
    (fun g h s => zOfCocycle_fst_mul S y hy hsub g h s)
    (fun g h s => zOfCocycle_snd_mul S y hy hsub g h s)
    (fun g h s => zOfCocycle_invariants S y hy hsub g h s)
  refine ⟨⟨Z, ?_⟩, fun g h => hZ g h⟩
  rw [mem_cocycles₂_def]
  intro q₁ q₂ q₃
  revert q₁ q₂ q₃
  rw [QuotientGroup.forall_mk]
  intro g
  rw [QuotientGroup.forall_mk]
  intro h
  rw [QuotientGroup.forall_mk]
  intro k
  apply Subtype.ext
  simp only [Submodule.coe_sub, Submodule.coe_add, ← QuotientGroup.mk'_apply]
  rw [quotientToInvariants_rho_apply, hZ h k, ← map_mul (QuotientGroup.mk' S) g h, hZ (g * h) k,
    ← map_mul (QuotientGroup.mk' S) h k, hZ g (h * k), hZ g h]
  exact (mem_cocycles₂_def (zOfCocycle S y hy hsub)).1 (zOfCocycle_mem_cocycles₂ S y hy hsub) g h k

/-- The action of `cochainsMap₂ f φ` on an explicit `2`-cochain. -/
lemma cochainsMap₂_apply {G' H' : Type} [Group G'] [Group H'] {A : Rep k H'} {B : Rep k G'}
    (f : G' →* H') (φ : Rep.res f A ⟶ B) (x : H' × H' → A) (g h : G') :
    (cochainsMap₂ f φ x) (g, h) = φ.hom (x (f g, f h)) := by
  simp [cochainsMap₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The range of the inflation `H²(G ⧸ S, A^S) → H²(G,A)` is contained in the kernel of the
restriction `H²(G,A) → H²(S,A)`. -/
lemma range_infNatTrans_le_ker_resNatTrans (S : Subgroup G) [S.Normal] (A : Rep k G) :
    LinearMap.range ((infNatTrans k S 2).app A).hom ≤
      LinearMap.ker ((resNatTrans k (G := S) (H := G) S.subtype 2).app A).hom := by
  rintro x ⟨y, rfl⟩
  induction y using H2_induction_on with | h y₀ =>
  rw [LinearMap.mem_ker]
  set ψ : Rep.res (QuotientGroup.mk' S) (A.quotientToInvariants S) ⟶ A :=
    Rep.ofHom (A.ρ.quotientToInvariants_lift S) with hψ
  have h1 : (infNatTrans k S 2).app A = map (QuotientGroup.mk' S) ψ 2 := rfl
  have h2 : (resNatTrans k (G := S) (H := G) S.subtype 2).app A
      = map S.subtype (𝟙 (Rep.res S.subtype A)) 2 := rfl
  rw [h1, h2]
  change (ConcreteCategory.hom (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2))
      ((ConcreteCategory.hom (groupCohomology.map (QuotientGroup.mk' S) ψ 2))
        ((ConcreteCategory.hom (H2π ((Rep.quotientToInvariantsFunctor k S).obj A))) y₀)) = 0
  have hA : (ConcreteCategory.hom (groupCohomology.map (QuotientGroup.mk' S) ψ 2))
      ((ConcreteCategory.hom (H2π ((Rep.quotientToInvariantsFunctor k S).obj A))) y₀)
      = (ConcreteCategory.hom (H2π A))
          ((ConcreteCategory.hom (mapCocycles₂ (QuotientGroup.mk' S) ψ)) y₀) :=
    H2π_comp_map_apply (QuotientGroup.mk' S) ψ y₀
  rw [hA]
  have hB : (ConcreteCategory.hom (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2))
      ((ConcreteCategory.hom (H2π A))
        ((ConcreteCategory.hom (mapCocycles₂ (QuotientGroup.mk' S) ψ)) y₀))
      = (ConcreteCategory.hom (H2π (Rep.res S.subtype A)))
          ((ConcreteCategory.hom (mapCocycles₂ S.subtype (𝟙 (Rep.res S.subtype A))))
            ((ConcreteCategory.hom (mapCocycles₂ (QuotientGroup.mk' S) ψ)) y₀)) :=
    H2π_comp_map_apply S.subtype (𝟙 (Rep.res S.subtype A)) _
  rw [hB, H2π_eq_zero_iff, coboundaries₂]
  refine ⟨fun _ : S => (y₀ (1, 1)).val, ?_⟩
  ext p
  obtain ⟨s, t⟩ := p
  rw [coe_mapCocycles₂, coe_mapCocycles₂, cochainsMap₂_apply, cochainsMap₂_apply]
  rw [show (QuotientGroup.mk' S) (S.subtype s) = 1 from
      (QuotientGroup.eq_one_iff (S.subtype s)).2 s.2,
    show (QuotientGroup.mk' S) (S.subtype t) = 1 from
      (QuotientGroup.eq_one_iff (S.subtype t)).2 t.2]
  simp only [Rep.hom_id, d₁₂_hom_apply, hψ]
  rw [((y₀ (1, 1)).2 s)]
  rw [show (y₀ (1, 1)).val - (y₀ (1, 1)).val + (y₀ (1, 1)).val = (y₀ (1, 1)).val from by abel]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **Exactness of the inflation–restriction sequence in degree 2.** -/
theorem H2_inflation_restriction_exact_of_subsingleton_H1_general {G : Type} [Group G]
    (S : Subgroup G) [S.Normal] (A : Rep k G)
    (hsub : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    LinearMap.range ((infNatTrans k S 2).app A).hom =
      LinearMap.ker ((resNatTrans k (G := S) (H := G) S.subtype 2).app A).hom := by
  classical
  refine le_antisymm (range_infNatTrans_le_ker_resNatTrans S A) ?_
  intro z hz
  induction z using H2_induction_on with | h x₀ =>
  rw [LinearMap.mem_ker] at hz
  set ψ : Rep.res (QuotientGroup.mk' S) (A.quotientToInvariants S) ⟶ A :=
    Rep.ofHom (A.ρ.quotientToInvariants_lift S) with hψ
  -- step 1: the restriction of `x₀` to `S` is a coboundary
  have hres : H2π (Rep.res S.subtype A)
      (mapCocycles₂ S.subtype (𝟙 (Rep.res S.subtype A)) x₀) = 0 := by
    have h := hz
    rw [show (resNatTrans k (G := S) (H := G) S.subtype 2).app A
        = map S.subtype (𝟙 (Rep.res S.subtype A)) 2 from rfl] at h
    change (ConcreteCategory.hom (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2))
      ((ConcreteCategory.hom (H2π A)) x₀) = 0 at h
    rw [H2π_comp_map_apply S.subtype (𝟙 (Rep.res S.subtype A)) x₀] at h
    exact h
  obtain ⟨w, hw⟩ : ∃ w : S → A,
      (d₁₂ (Rep.res S.subtype A)).hom w
        = ⇑(mapCocycles₂ S.subtype (𝟙 (Rep.res S.subtype A)) x₀) := by
    have hmem : (⇑(mapCocycles₂ S.subtype (𝟙 (Rep.res S.subtype A)) x₀) : S × S → A)
        ∈ coboundaries₂ (Rep.res S.subtype A) := (H2π_eq_zero_iff _).1 hres
    rwa [coboundaries₂, LinearMap.mem_range] at hmem
  -- step 2: correct `x₀` by a coboundary so that it vanishes on `S × S`
  let wtilde : G → A := fun g => if hg : g ∈ S then w ⟨g, hg⟩ else 0
  have hwtilde : ∀ s : S, wtilde s.1 = w s := by
    intro s
    simp only [wtilde]
    rw [dif_pos s.2]
  let yfun : G × G → A := fun p => x₀ p - (d₁₂ A).hom wtilde p
  have hyfun_mem : yfun ∈ cocycles₂ A := by
    have h1 : (fun p : G × G => (d₁₂ A).hom wtilde p) ∈ cocycles₂ A :=
      d₁₂_apply_mem_cocycles₂ wtilde
    have h2 : (fun p : G × G => x₀ p) ∈ cocycles₂ A := x₀.2
    have h := sub_mem h2 h1
    convert h using 1
  have hy_SS : ∀ s t : S, yfun (s.1, t.1) = 0 := by
    intro s t
    have hd : (d₁₂ A).hom wtilde (s.1, t.1) = x₀ (s.1, t.1) := by
      have hwpt := congr_fun hw (s, t)
      have h1 : (d₁₂ A).hom wtilde (s.1, t.1)
          = (d₁₂ (Rep.res S.subtype A)).hom w (s, t) := by
        show A.ρ s.1 (wtilde t.1) - wtilde (s.1 * t.1) + wtilde s.1
          = A.ρ s.1 (w t) - w (s * t) + w s
        rw [hwtilde s, hwtilde t, hwtilde ⟨s.1 * t.1, S.mul_mem s.2 t.2⟩]
        rfl
      have h2 : (⇑(mapCocycles₂ S.subtype (𝟙 (Rep.res S.subtype A)) x₀)) (s, t)
          = x₀ (s.1, t.1) := by
        rw [coe_mapCocycles₂, cochainsMap₂_apply]
        simp
      rw [h1, hwpt, h2]
    rw [show yfun (s.1, t.1) = x₀ (s.1, t.1) - (d₁₂ A).hom wtilde (s.1, t.1) from rfl, hd,
      sub_self]
  -- step 3: produce the descended cocycle
  obtain ⟨x₁, hx₁⟩ :=
    exists_cocycle_quotient_of_vanishing S ⟨yfun, hyfun_mem⟩ hy_SS hsub
  refine ⟨H2π (A.quotientToInvariants S) x₁, ?_⟩
  rw [show (infNatTrans k S 2).app A = map (QuotientGroup.mk' S) ψ 2 from rfl]
  change (ConcreteCategory.hom (groupCohomology.map (QuotientGroup.mk' S) ψ 2))
      ((ConcreteCategory.hom (H2π ((Rep.quotientToInvariantsFunctor k S).obj A))) x₁)
      = (ConcreteCategory.hom (H2π A)) x₀
  rw [show (ConcreteCategory.hom (groupCohomology.map (QuotientGroup.mk' S) ψ 2))
      ((ConcreteCategory.hom (H2π ((Rep.quotientToInvariantsFunctor k S).obj A))) x₁)
      = (ConcreteCategory.hom (H2π A))
          ((ConcreteCategory.hom (mapCocycles₂ (QuotientGroup.mk' S) ψ)) x₁) from
    H2π_comp_map_apply (QuotientGroup.mk' S) ψ x₁]
  rw [H2π_eq_iff]
  have hz₁ : (⇑(mapCocycles₂ (QuotientGroup.mk' S) ψ x₁) : G × G → A)
      = zOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub := by
    funext p
    obtain ⟨g, h⟩ := p
    rw [coe_mapCocycles₂, cochainsMap₂_apply, hψ]
    show ((x₁ ((QuotientGroup.mk' S) g, (QuotientGroup.mk' S) h)) : A)
      = zOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub (g, h)
    exact hx₁ g h
  have hEq : (⇑(mapCocycles₂ (QuotientGroup.mk' S) ψ x₁) : G × G → A) - ⇑x₀
      = -(fun p : G × G => (d₁₂ A).hom wtilde p)
        - (d₁₂ A).hom (uOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub) := by
    funext p
    have hp : (⇑(mapCocycles₂ (QuotientGroup.mk' S) ψ x₁) : G × G → A) p
        = zOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub p := congr_fun hz₁ p
    change (⇑(mapCocycles₂ (QuotientGroup.mk' S) ψ x₁) : G × G → A) p - x₀ p
        = -(d₁₂ A).hom wtilde p - (d₁₂ A).hom (uOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub) p
    rw [hp]
    show (yfun p - (d₁₂ A).hom (uOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub) p) - x₀ p
        = -(d₁₂ A).hom wtilde p - (d₁₂ A).hom (uOfCocycle S ⟨yfun, hyfun_mem⟩ hy_SS hsub) p
    simp only [yfun]
    abel
  rw [hEq]
  exact sub_mem (neg_mem (LinearMap.mem_range.2 ⟨wtilde, rfl⟩))
    (LinearMap.mem_range.2 ⟨_, rfl⟩)

/-- **Exactness of the inflation–restriction sequence in degree 2** (CoNF XII, proof of
(12.2.1)): if `H¹(S, A) = 0` for a normal subgroup `S ◁ G`, then
`H²(G ⧸ S, A^S) --inf--> H²(G, A) --res--> H²(S, A)` is exact at `H²(G, A)`. -/
theorem H2_inflation_restriction_exact_of_subsingleton_H1 {G : Type} [Group G]
    (S : Subgroup G) [S.Normal] (A : Rep ℤ G)
    (h : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    LinearMap.range ((groupCohomology.infNatTrans ℤ S 2).app A).hom =
      LinearMap.ker
        ((groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype 2).app A).hom :=
  H2_inflation_restriction_exact_of_subsingleton_H1_general S A h

end Commons.RepresentationTheory.GroupCohomology