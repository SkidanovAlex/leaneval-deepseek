import Mathlib
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.card_weight_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-! ### Auxiliary lemmas

We collect here the elementary ingredients of the argument: monomials in powers of an ideal,
the coefficients of an element of a finitely generated ideal, a telescoping lemma for chains
of `Order.coheight` bounds, and the stars-and-bars count of monomials of degree `≤ T`.
-/

/-- A monomial `∏ i, u i ^ (β i)` of degree `∑ i, β i` in elements of an ideal `𝔓` lies in the
corresponding power `𝔓 ^ (∑ i, β i)`. -/
lemma monoPow_mem_pow {R : Type*} [CommRing R] {ℓ : ℕ} {u : Fin ℓ → R} {𝔓 : Ideal R}
    (hu : ∀ i, u i ∈ 𝔓) (β : Fin ℓ → ℕ) : monoPow u β ∈ 𝔓 ^ (∑ i, β i) := by
  have key : ∀ s : Finset (Fin ℓ), (∏ i ∈ s, u i ^ β i) ∈ 𝔓 ^ (∑ i ∈ s, β i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Ideal.IsTwoSided.pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hu a) (β a)) ih
  simpa [monoPow] using key Finset.univ

/-- Every element of the ideal spanned by the image of a finite set `P` under `f` is a finite
`R`-linear combination of the values of `f` on `P`, indexed by `P` itself. -/
lemma exists_coeff_of_mem_span_image {R : Type*} [CommRing R] {ι : Type*} (P : Finset ι)
    (f : ι → R) {x : R} (hx : x ∈ Ideal.span (f '' (P : Set ι))) :
    ∃ c : ι → R, x = ∑ i ∈ P, c i * f i := by
  classical
  induction P using Finset.induction_on generalizing x with
  | empty =>
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    have hle : Ideal.span (f '' (↑(∅ : Finset ι) : Set ι)) ≤ ⊥ := by
      rw [Finset.coe_empty, Set.image_empty]
      simp
    have hx0 : x ∈ (⊥ : Ideal R) := hle hx
    simpa using hx0
  | insert a P ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq] at hx
    have hle : Ideal.span (insert (f a) (f '' (↑P : Set ι)))
        ≤ Ideal.span {f a} ⊔ Ideal.span (f '' (↑P : Set ι)) := by
      refine Ideal.span_le.mpr ?_
      intro y hy
      rw [Set.mem_insert_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact Submodule.mem_sup_left (Ideal.subset_span (by simp))
      · exact Submodule.mem_sup_right (Ideal.subset_span hy)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle hx)
    obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton' (x := y) (y := f a)).mp hy
    obtain ⟨c, hc⟩ := ih hz
    refine ⟨fun i => if i = a then w else c i, ?_⟩
    have hval : (fun i => if i = a then w else c i) a * f a = w * f a := by simp
    have hsumP : (∑ i ∈ P, (fun i => if i = a then w else c i) i * f i)
        = ∑ i ∈ P, c i * f i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hne : i ≠ a := fun h => ha (h ▸ hi)
      simp [hne]
    rw [Finset.sum_insert ha, hval, hsumP, ← hc, hw]
    exact hyz.symm

/-- Telescoping a chain of coheight bounds: if `coheight (F τ) + N τ ≤ coheight (F (τ+1))` for
every `τ ≤ T`, then `coheight (F 0) + ∑_{τ ≤ T} N τ ≤ coheight (F (T+1))`. -/
lemma coheight_chain_range {α : Type*} [Preorder α] (F : ℕ → α) (N : ℕ → ℕ) (T : ℕ)
    (h : ∀ τ, τ ≤ T → Order.coheight (F τ) + (N τ : ℕ∞) ≤ Order.coheight (F (τ + 1))) :
    Order.coheight (F 0) + (((∑ τ ∈ Finset.range (T + 1), N τ) : ℕ) : ℕ∞) ≤
      Order.coheight (F (T + 1)) := by
  induction T with
  | zero => simpa [Finset.sum_range_one] using h 0 le_rfl
  | succ T ih =>
    have hih := ih (fun τ hτ => h τ (le_trans hτ (by omega : T ≤ T + 1)))
    have hlast := h (T + 1) le_rfl
    rw [Finset.sum_range_succ, Nat.cast_add, ← add_assoc]
    exact le_trans (add_le_add hih le_rfl) hlast

/-- `weightFinset ℓ τ` is the degree-`τ` fibre of the set of multi-indices of degree `≤ T`. -/
private lemma weightFinset_eq_filter_aux {ℓ T τ : ℕ} (hτ : τ ≤ T) :
    weightFinset ℓ τ =
      ((Fintype.piFinset (fun _ : Fin ℓ => Finset.range (T + 1))).filter
        (fun β : Fin ℓ → ℕ => ∑ i, β i ≤ T)).filter (fun β : Fin ℓ → ℕ => ∑ i, β i = τ) := by
  ext β
  simp only [weightFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun i => by have := h1 i; omega, by omega⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun i => ?_, h3⟩
    have hle : β i ≤ ∑ j, β j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

/-- The multi-indices of degree exactly `τ` (`τ ≤ T`) partition those of degree `≤ T`, so the
sum of their cardinalities is the binomial coefficient `C(T+ℓ, ℓ)`. -/
theorem sum_weightFinset_card {ℓ T : ℕ} :
    (∑ τ ∈ Finset.range (T + 1), (weightFinset ℓ τ).card) = (T + ℓ).choose ℓ := by
  classical
  rw [← card_weight_le (ℓ := ℓ) (T := T)]
  have hmaps : Set.MapsTo (fun β : Fin ℓ → ℕ => ∑ i, β i)
      (↑((Fintype.piFinset (fun _ : Fin ℓ => Finset.range (T + 1))).filter
        (fun β : Fin ℓ → ℕ => ∑ i, β i ≤ T)) : Set (Fin ℓ → ℕ))
      (↑(Finset.range (T + 1))) := by
    intro β hβ
    have hle : ∑ i, β i ≤ T := (Finset.mem_filter.mp hβ).2
    have hmem : ∑ i, β i ∈ Finset.range (T + 1) := by
      rw [Finset.mem_range]
      omega
    simpa using hmem
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun τ hτ => ?_)
  have hτT : τ ≤ T := by
    have := Finset.mem_range.mp hτ
    omega
  rw [← weightFinset_eq_filter_aux (T := T) hτT]

/-! ### The chain of ideals

`cohF J u τ = J + (monoPow u β : |β| ≥ τ)` is the chain along which the independence hypothesis
gives successive coincrements of the coheight.  `cohG A u P = A + (monoPow u β : β ∈ P)` is the
intermediate ideal obtained by adjoining the monomials of a finite set `P` one at a time. -/

/-- The ideal `F_τ = J + (monoPow u β : ∑ βᵢ ≥ τ)`. -/
noncomputable def cohF {R : Type*} [CommRing R] {ℓ : ℕ} (J : Ideal R) (u : Fin ℓ → R) (τ : ℕ) :
    Ideal R :=
  J ⊔ Ideal.span ((fun β : Fin ℓ → ℕ => monoPow u β) '' {β : Fin ℓ → ℕ | τ ≤ ∑ i, β i})

/-- `cohG A u P = A + (monoPow u β : β ∈ P)`. -/
noncomputable def cohG {R : Type*} [CommRing R] {ℓ : ℕ} (A : Ideal R) (u : Fin ℓ → R)
    (P : Finset (Fin ℓ → ℕ)) : Ideal R :=
  A ⊔ Ideal.span ((fun β : Fin ℓ → ℕ => monoPow u β) '' (P : Set (Fin ℓ → ℕ)))

lemma le_cohF {R : Type*} [CommRing R] {ℓ : ℕ} (J : Ideal R) (u : Fin ℓ → R) (τ : ℕ) :
    J ≤ cohF J u τ := le_sup_left

lemma cohF_anti {R : Type*} [CommRing R] {ℓ : ℕ} (J : Ideal R) (u : Fin ℓ → R) {τ σ : ℕ}
    (h : τ ≤ σ) : cohF J u σ ≤ cohF J u τ :=
  sup_le_sup_left (Ideal.span_mono (Set.image_mono (fun _ hβ => le_trans h hβ))) J

lemma cohF_le_add_pow {R : Type*} [CommRing R] {ℓ : ℕ} (J 𝔓 : Ideal R) (u : Fin ℓ → R)
    (hu : ∀ i, u i ∈ 𝔓) (τ : ℕ) : cohF J u τ ≤ J + 𝔓 ^ τ := by
  rw [Ideal.add_eq_sup]
  refine sup_le le_sup_left ?_
  refine Ideal.span_le.mpr ?_
  rintro x ⟨β, hβ, rfl⟩
  exact Submodule.mem_sup_right (Ideal.pow_le_pow_right hβ (monoPow_mem_pow hu β))

lemma cohF_zero {R : Type*} [CommRing R] {ℓ : ℕ} (J : Ideal R) (u : Fin ℓ → R) :
    cohF J u 0 = ⊤ := by
  have hmem : (1 : R) ∈
      Ideal.span ((fun β : Fin ℓ → ℕ => monoPow u β) '' {β : Fin ℓ → ℕ | 0 ≤ ∑ i, β i}) :=
    Ideal.subset_span ⟨0, by simp, by simp [monoPow]⟩
  have hsp : Ideal.span ((fun β : Fin ℓ → ℕ => monoPow u β) ''
      {β : Fin ℓ → ℕ | 0 ≤ ∑ i, β i}) = ⊤ := (Ideal.eq_top_iff_one _).mpr hmem
  rw [cohF, hsp, sup_top_eq]

lemma cohG_insert {R : Type*} [CommRing R] {ℓ : ℕ} {A : Ideal R} {u : Fin ℓ → R}
    {P : Finset (Fin ℓ → ℕ)} {a : Fin ℓ → ℕ} (_ha : a ∉ P) :
    cohG A u (insert a P) = cohG A u P ⊔ Ideal.span {monoPow u a} := by
  simp only [cohG, Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert]
  ac_rfl

/-! ### The main theorem -/

/-- The chain behind Wüstholz's multiplicity estimate. Let `J ≤ 𝔓` be ideals, `u₁,…,u_ℓ ∈ 𝔓`
and suppose that modulo `J + 𝔓^{τ+1}` the degree-`τ` monomials in the `uᵢ` are independent over
`R` in the following sense: if `∑_{|β|=τ} C β · u^β ∈ J + 𝔓^{τ+1}` then `C α ∈ 𝔓` for every `α`
of degree `τ` (`τ ≤ T`). Then `J` has coheight at least the number `C(T+ℓ,ℓ)` of monomials of
degree `≤ T`.

Proof sketch. Put `F_τ := J + Ideal.span (monoPow u β : |β| ≥ τ)` for `τ = 1..T+1`, so
`F_{T+1} ⊆ … ⊆ F_1 ≤ 𝔓 < ⊤` and `J ≤ F_{T+1} ≤ F_1`.
* Strictness. For `P ⊆ weightFinset ℓ τ`, the ideal `G(P) := F_{τ+1} + Ideal.span (monoPow u β : β ∈ P)`
satisfies `G(P) < G(P ∪ {β})` for `β ∈ weightFinset ℓ τ \ P`: the supports of the two ideals
differ by `monoPow u β`, and if `monoPow u β ∈ G(P)` then writing that membership as
`monoPow u β - ∑_{γ∈P} c γ * monoPow u γ = f ∈ F_{τ+1} ⊆ J + 𝔓^{τ+1}` exhibits the left side as
`∑_{|α|=τ} C α * monoPow u α` with `C β = 1`, so the hypothesis gives `1 ∈ 𝔓`, contradiction.
(Similarly `G(weightFinset ℓ 0) = ⊤` at `τ = 0`, using `F_1 ≤ 𝔓 < ⊤`.)
* Finset induction over `P` using `Order.coheight_add_one_le` (a strict inclusion of ideals
gives `coheight y + 1 ≤ coheight x`) yields, at `P = ∅`,
`coheight F_{τ+1} ≥ coheight F_τ + #(weightFinset ℓ τ)` for every `τ ≤ T`, and the `τ = 0` case
gives `coheight ⊤ + 1 ≤ coheight F_1`, i.e. `1 ≤ coheight F_1`.
* Chaining these `T+1` inequalities from `F_{T+1}` up to `F_1` and using
`∑_{τ ≤ T} #(weightFinset ℓ τ) = (T+ℓ).choose ℓ` (`card_weight_le`, counting the multi-indices of
degree `≤ T`) and `coheight F_1 ≤ coheight J` (from `J ≤ F_1`) gives the claim. -/
theorem coheight_ge_of_indep {R : Type*} [CommRing R] {ℓ T : ℕ} (J 𝔓 : Ideal R) (u : Fin ℓ → R)
    (hJ𝔓 : J ≤ 𝔓) (h𝔓top : 𝔓 ≠ ⊤) (hu : ∀ i, u i ∈ 𝔓)
    (hind : ∀ τ : ℕ, τ ≤ T → ∀ C : (Fin ℓ → ℕ) → R,
      (∑ β ∈ weightFinset ℓ τ, C β * monoPow u β) ∈ J + 𝔓 ^ (τ + 1) →
      ∀ α ∈ weightFinset ℓ τ, C α ∈ 𝔓) :
    (((T + ℓ).choose ℓ : ℕ) : ℕ∞) ≤ Order.coheight J := by
  classical
  -- The hypothesis `J ≤ 𝔓` is not needed by the argument below: the chain `cohF J u τ` is
  -- compared with `𝔓` only through `cohF_le_add_pow`, and the base of the chain is
  -- `cohF J u 0 = ⊤`.  We record it here for reference (it says the whole chain lives below `𝔓`).
  have _hJ𝔓 : J ≤ 𝔓 := hJ𝔓
  -- ### Generalisation of the independence hypothesis to arbitrary finite sets of coefficients
  have hindS : ∀ (τ : ℕ), τ ≤ T → ∀ S : Finset (Fin ℓ → ℕ), S ⊆ weightFinset ℓ τ →
      ∀ C : (Fin ℓ → ℕ) → R,
      (∑ β ∈ S, C β * monoPow u β) ∈ J + 𝔓 ^ (τ + 1) → ∀ α ∈ S, C α ∈ 𝔓 := by
    intro τ hτ S hS C hC α hα
    have hsum : (∑ β ∈ S, C β * monoPow u β)
        = ∑ β ∈ weightFinset ℓ τ, (if β ∈ S then C β else 0) * monoPow u β := by
      rw [← Finset.sum_subset hS (fun x _ hxS => by simp [hxS])]
      exact Finset.sum_congr rfl (fun x hx => by simp [hx])
    rw [hsum] at hC
    have hβ := hind τ hτ (fun β => if β ∈ S then C β else 0) hC α (hS hα)
    simpa [hα] using hβ
  -- ### Strictness of the chain `G P < G (insert β P)`
  have hstrict : ∀ (τ : ℕ), τ ≤ T → ∀ P : Finset (Fin ℓ → ℕ), P ⊆ weightFinset ℓ τ →
      ∀ β ∈ weightFinset ℓ τ, β ∉ P →
      cohG (cohF J u (τ + 1)) u P < cohG (cohF J u (τ + 1)) u (insert β P) := by
    intro τ hτ P hP β hβ hβP
    rw [cohG_insert hβP]
    refine lt_of_le_of_ne le_sup_left (fun heq => ?_)
    -- `monoPow u β` lies in `G P`: split it as `f + s` with `f ∈ F_{τ+1}`, `s` a `P`-combination
    have hm : monoPow u β ∈ cohG (cohF J u (τ + 1)) u P := by
      rw [heq]
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self (monoPow u β))
    obtain ⟨f, hf, s, hs, hfs⟩ := Submodule.mem_sup.mp hm
    obtain ⟨c, hc⟩ := exists_coeff_of_mem_span_image P (fun γ => monoPow u γ) hs
    -- `monoPow u β - s = f ∈ F_{τ+1} ≤ J + 𝔓^{τ+1}`
    have hmem : monoPow u β - s ∈ J + 𝔓 ^ (τ + 1) := by
      have hfs' : monoPow u β - s = f := by rw [← hfs]; abel
      rw [hfs']
      exact cohF_le_add_pow J 𝔓 u hu (τ + 1) hf
    -- exhibit the difference as a `weightFinset ℓ τ`-combination with coefficient `1` at `β`
    set d : (Fin ℓ → ℕ) → R :=
      fun γ => if γ = β then 1 else if γ ∈ P then -(c γ) else 0 with hd
    have hdβ : d β = 1 := by simp [hd]
    have hdP : ∀ γ ∈ P, d γ = -(c γ) := by
      intro γ hγ
      have hne : γ ≠ β := fun h => hβP (h ▸ hγ)
      simp [hd, hne, hγ]
    have hsumd : (∑ γ ∈ insert β P, d γ * monoPow u γ) = monoPow u β - s := by
      rw [Finset.sum_insert hβP, hdβ, one_mul]
      have hstep : ∀ γ ∈ P, d γ * monoPow u γ = -(c γ * monoPow u γ) := by
        intro γ hγ
        rw [hdP γ hγ, neg_mul]
      rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib, ← hc]
      abel
    have hmemd : (∑ γ ∈ insert β P, d γ * monoPow u γ) ∈ J + 𝔓 ^ (τ + 1) := by
      rw [hsumd]
      exact hmem
    have hSins : insert β P ⊆ weightFinset ℓ τ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rwa [h]
      · exact hP h
    have h1 : (1 : R) ∈ 𝔓 := by
      have hdβmem := hindS τ hτ (insert β P) hSins d hmemd β (Finset.mem_insert_self β P)
      rwa [hdβ] at hdβmem
    exact h𝔓top ((Ideal.eq_top_iff_one 𝔓).mpr h1)
  -- ### Each level of the chain contributes `#(weightFinset ℓ τ)` to the coheight
  have hchain : ∀ τ ≤ T, Order.coheight (cohF J u τ) + (((weightFinset ℓ τ).card : ℕ) : ℕ∞)
      ≤ Order.coheight (cohF J u (τ + 1)) := by
    intro τ hτ
    have key : ∀ P : Finset (Fin ℓ → ℕ), P ⊆ weightFinset ℓ τ →
        Order.coheight (cohG (cohF J u (τ + 1)) u P) + (((P.card : ℕ) : ℕ∞))
          ≤ Order.coheight (cohF J u (τ + 1)) := by
      intro P
      induction P using Finset.induction_on with
      | empty =>
        intro _
        simp [cohG]
      | insert a P ha ih =>
        intro hP
        have haW : a ∈ weightFinset ℓ τ := hP (Finset.mem_insert_self a P)
        have hPW : P ⊆ weightFinset ℓ τ := fun x hx => hP (Finset.mem_insert_of_mem hx)
        have hih := ih hPW
        have hstr := hstrict τ hτ P hPW a haW ha
        have h1 : Order.coheight (cohG (cohF J u (τ + 1)) u (insert a P)) + 1
            ≤ Order.coheight (cohG (cohF J u (τ + 1)) u P) := Order.coheight_add_one_le hstr
        have hcard : ((((insert a P).card : ℕ)) : ℕ∞) = (((P.card : ℕ)) : ℕ∞) + 1 := by
          rw [Finset.card_insert_of_notMem ha]
          simp
        calc Order.coheight (cohG (cohF J u (τ + 1)) u (insert a P))
              + ((((insert a P).card : ℕ)) : ℕ∞)
            = Order.coheight (cohG (cohF J u (τ + 1)) u (insert a P))
              + ((((P.card : ℕ)) : ℕ∞) + 1) := by rw [hcard]
          _ = (Order.coheight (cohG (cohF J u (τ + 1)) u (insert a P)) + 1)
              + (((P.card : ℕ)) : ℕ∞) := by ac_rfl
          _ ≤ Order.coheight (cohG (cohF J u (τ + 1)) u P) + (((P.card : ℕ)) : ℕ∞) :=
              add_le_add h1 le_rfl
          _ ≤ Order.coheight (cohF J u (τ + 1)) := hih
    have hW := key (weightFinset ℓ τ) (fun x hx => hx)
    -- the top of the level-`τ` chain lies below `F_τ`
    have hGWle : cohG (cohF J u (τ + 1)) u (weightFinset ℓ τ) ≤ cohF J u τ := by
      refine sup_le (cohF_anti J u (by omega : τ ≤ τ + 1)) ?_
      refine Ideal.span_le.mpr ?_
      rintro x ⟨γ, hγ, rfl⟩
      refine Submodule.mem_sup_right ?_
      refine Ideal.subset_span ⟨γ, ?_, rfl⟩
      have hsumγ : ∑ i, γ i = τ := (Finset.mem_filter.mp hγ).2
      exact hsumγ.ge
    have hle : Order.coheight (cohF J u τ)
        ≤ Order.coheight (cohG (cohF J u (τ + 1)) u (weightFinset ℓ τ)) :=
      Order.coheight_anti hGWle
    calc Order.coheight (cohF J u τ) + (((weightFinset ℓ τ).card : ℕ) : ℕ∞)
        ≤ Order.coheight (cohG (cohF J u (τ + 1)) u (weightFinset ℓ τ))
          + (((weightFinset ℓ τ).card : ℕ) : ℕ∞) := add_le_add hle le_rfl
      _ ≤ Order.coheight (cohF J u (τ + 1)) := hW
  -- ### Telescoping and the final count
  have hF0 : Order.coheight (cohF J u 0) = 0 := by simp [cohF_zero]
  have htel := coheight_chain_range (fun τ => cohF J u τ)
    (fun τ => (weightFinset ℓ τ).card) T hchain
  have hbig : (((T + ℓ).choose ℓ : ℕ) : ℕ∞) ≤ Order.coheight (cohF J u (T + 1)) := by
    simpa [hF0, sum_weightFinset_card] using htel
  exact le_trans hbig (Order.coheight_anti (le_cohF J u (T + 1)))

end Work.BW
