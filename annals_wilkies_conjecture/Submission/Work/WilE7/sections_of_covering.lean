/-
  Area WilE7: the vertical fibration over a set `C ⊆ ℝⁿ` whose fibres have constant
  cardinality, and whose projection is a covering map, has `q` *continuous ordered sections*.

  `Work.WilE7.sections_of_covering` is the topological input of this area: if
  `S ⊆ ℝ^{n+1}` projects onto `C ⊆ ℝⁿ` by `z ↦ Fin.init z`, the projection is a covering
  map and every fibre `{y | Fin.snoc x y ∈ S}`, `x ∈ C`, has exactly `q > 0` elements, then
  the elements of the fibre over `x` can be listed increasingly,
  `s 0 x < s 1 x < … < s (q-1) x`, with every `s j` continuous on `C`, and with every point
  of `S` reached.

  The proof has two halves.

  * *Order theory.*  `Work.WilE7.eventually_orderEmbOfFin`: if a family of finite sets of
    reals has `q` elements everywhere and, near a point `x₀`, functions `e j` continuous at
    `x₀` enumerate `F x₀` increasingly and take their values in `F`, then near `x₀` the `e j`
    *are* the increasing enumeration of `F`.  This is `Finset.orderEmbOfFin_unique` plus
    continuity (`ContinuousAt.eventually_lt`).

  * *Covering theory.*  The projection is a local homeomorphism, so through every point of
    the fibration above `x₀` there is a continuous local section
    `OpenPartialHomeomorph C S` of the projection
    (`IsCoveringMap.isLocalHomeomorph` and `IsLocalHomeomorph.localInverseAt`); evaluating
    such a section at a nearby base point gives a point of `S` whose last coordinate is the
    corresponding element of the fibre (`Work.WilE7.section_eq_snoc`).

  Combining the two halves at each point `x₀ ∈ C` shows that the `j`-th smallest element of
  the fibre is continuous at `x₀`: locally it is the `j`-th continuous local section, the
  enumeration of the fibre over a nearby point being forced by the order-theoretic lemma.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.section_eq_snoc

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7

/-! ## Ordering a varying finite set of reals -/

/-- **Ordering lemma.** If `F x` is a finite set of reals with `q` elements for every `x`,
if functions `e j` are continuous at `x₀` and enumerate `F x₀` increasingly, and if near `x₀`
all their values lie in `F`, then near `x₀` the functions `e j` coincide with the increasing
enumeration `Finset.orderEmbOfFin` of `F`.

The point is that a strictly increasing map `Fin q → ℝ` whose values all lie in a finite set
of cardinality `q` must be its increasing enumeration
(`Finset.orderEmbOfFin_unique`); strict monotonicity is inherited from `x₀` by continuity. -/
theorem eventually_orderEmbOfFin {α : Type*} [TopologicalSpace α] {q : ℕ}
    {F : α → Finset ℝ} (hcard : ∀ x, (F x).card = q) {x₀ : α} {e : Fin q → α → ℝ}
    (hcont : ∀ j, ContinuousAt (e j) x₀)
    (h₀ : ∀ j, e j x₀ = (F x₀).orderEmbOfFin (hcard x₀) j)
    (hmem : ∀ᶠ y in nhds x₀, ∀ j, e j y ∈ F y) :
    ∀ᶠ y in nhds x₀, ∀ j, e j y = (F y).orderEmbOfFin (hcard y) j := by
  have hmono : ∀ᶠ y in nhds x₀, StrictMono fun j => e j y := by
    have hpair : ∀ᶠ y in nhds x₀, ∀ p : Fin q × Fin q, p.1 < p.2 → e p.1 y < e p.2 y := by
      rw [Filter.eventually_all]
      intro p
      by_cases hp : p.1 < p.2
      · have hlt : e p.1 x₀ < e p.2 x₀ := by
          rw [h₀ p.1, h₀ p.2]
          exact (Finset.orderEmbOfFin (F x₀) (hcard x₀)).strictMono hp
        exact ((hcont p.1).eventually_lt (hcont p.2) hlt).mono fun y hy => fun _ => hy
      · exact Filter.Eventually.of_forall fun y hy => absurd hy hp
    filter_upwards [hpair] with y hy
    exact fun j k hjk => hy (j, k) hjk
  filter_upwards [hmono, hmem] with y hy hm
  intro j
  exact congrFun (Finset.orderEmbOfFin_unique (hcard y) hm hy) j

/-! ## The vertical fibre of the projection `z ↦ Fin.init z` -/

/-- The vertical fibre of `S` over `x : ℝⁿ`: the set of `y : ℝ` with `(x, y) ∈ S`. -/
def Fib {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) (x : Fin n → ℝ) : Set ℝ := {y | Fin.snoc x y ∈ S}

theorem mem_Fib {n : ℕ} {S : Set (Fin (n + 1) → ℝ)} {x : Fin n → ℝ} {y : ℝ} :
    y ∈ Fib S x ↔ Fin.snoc x y ∈ S := Iff.rfl

/-- The fibre over a point of `C` is finite, its cardinality `q` being positive. -/
theorem fibFinite {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) {x : Fin n → ℝ} (hx : x ∈ C) :
    (Fib S x).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [hfib x hx]; exact Nat.pos_iff_ne_zero.mp hq)

/-- The fibre over `x ∈ C`, as a finset of reals. -/
noncomputable def fibFinset {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (x : Fin n → ℝ) (hx : x ∈ C) :
    Finset ℝ := (fibFinite hq hfib hx).toFinset

theorem mem_fibFinset {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (x : Fin n → ℝ) (hx : x ∈ C) (y : ℝ) :
    y ∈ fibFinset hq hfib x hx ↔ Fin.snoc x y ∈ S :=
  Set.Finite.mem_toFinset (fibFinite hq hfib hx)

theorem fibFinset_card {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (x : Fin n → ℝ) (hx : x ∈ C) :
    (fibFinset hq hfib x hx).card = q := by
  rw [fibFinset, ← Set.ncard_eq_toFinset_card (Fib S x) (fibFinite hq hfib hx)]
  exact hfib x hx

/-! ## The `j`-th element of the fibre -/

/-- The `j`-th smallest element of the fibre over `x` (with junk value `0` off `C`). -/
noncomputable def sect {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (j : Fin q) (x : Fin n → ℝ) : ℝ :=
  if hx : x ∈ C then (fibFinset hq hfib x hx).orderEmbOfFin (fibFinset_card hq hfib x hx) j else 0

theorem sect_eq {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (j : Fin q) (x : Fin n → ℝ)
    (hx : x ∈ C) :
    sect hq hfib j x = (fibFinset hq hfib x hx).orderEmbOfFin (fibFinset_card hq hfib x hx) j := by
  rw [sect, dite_eq_left hx]

/-- The `j`-th element of the fibre really is in the fibre. -/
theorem sect_snoc_mem {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (j : Fin q) (x : Fin n → ℝ)
    (hx : x ∈ C) : Fin.snoc x (sect hq hfib j x) ∈ S := by
  rw [sect_eq hq hfib j x hx]
  exact (mem_fibFinset hq hfib x hx _).mp (Finset.orderEmbOfFin_mem _ _ j)

/-- The fibre over `x ∈ C`, listed increasingly in `j`. -/
theorem strictMono_sect {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (x : Fin n → ℝ) (hx : x ∈ C) :
    StrictMono fun j : Fin q => sect hq hfib j x := by
  intro a b hab
  simp only [sect_eq hq hfib a x hx, sect_eq hq hfib b x hx]
  exact (Finset.orderEmbOfFin (fibFinset hq hfib x hx) (fibFinset_card hq hfib x hx)).strictMono hab

/-- Every element of `S` occurs as the last coordinate of a point `Fin.snoc x (sect j x)`. -/
theorem exists_sect_eq {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hS : S ⊆ {z | Fin.init z ∈ C})
    (hfib : ∀ x ∈ C, (Fib S x).ncard = q) {z : Fin (n + 1) → ℝ} (hz : z ∈ S) :
    ∃ j : Fin q, z (Fin.last n) = sect hq hfib j (Fin.init z) := by
  have hx : Fin.init z ∈ C := hS hz
  have hy : z (Fin.last n) ∈ fibFinset hq hfib (Fin.init z) hx :=
    (mem_fibFinset hq hfib (Fin.init z) hx _).mpr (by rw [Fin.snoc_init_self]; exact hz)
  have hrange : z (Fin.last n) ∈ Set.range
      ((fibFinset hq hfib (Fin.init z) hx).orderEmbOfFin (fibFinset_card hq hfib (Fin.init z) hx)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hy
  obtain ⟨j, hj⟩ := hrange
  exact ⟨j, by rw [sect_eq hq hfib j (Fin.init z) hx]; exact hj.symm⟩

/-! ## The fibre as a function of the base point -/

/-- The fibre over a point of `C`, as a function on `C`. -/
noncomputable def fibFun {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (v : C) : Finset ℝ :=
  fibFinset hq hfib v.1 v.2

theorem fibFun_card {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hfib : ∀ x ∈ C, (Fib S x).ncard = q) (v : C) : (fibFun hq hfib v).card = q :=
  fibFinset_card hq hfib v.1 v.2

/-! ## Continuity of the ordered sections -/

/-- The core of the proof: at each point of `C`, the `j`-th element of the fibre is locally
one of the `q` continuous local sections provided by the covering map, hence continuous. -/
theorem continuousOn_sect {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hS : S ⊆ {z | Fin.init z ∈ C})
    (hfib : ∀ x ∈ C, (Fib S x).ncard = q)
    (hcov : IsCoveringMap fun z : S => (⟨Fin.init z.1, hS z.2⟩ : C)) (j : Fin q) :
    ContinuousOn (sect hq hfib j) C := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_continuousAt.mpr fun v₀ => ?_
  -- the points of `S` above `v₀`, and continuous local sections through them
  have hy : ∀ j : Fin q,
      (fibFun hq hfib v₀).orderEmbOfFin (fibFun_card hq hfib v₀) j ∈ fibFun hq hfib v₀ :=
    fun j => Finset.orderEmbOfFin_mem _ _ j
  let z : Fin q → S := fun j =>
    ⟨Fin.snoc v₀.1 ((fibFun hq hfib v₀).orderEmbOfFin (fibFun_card hq hfib v₀) j),
      (mem_fibFinset hq hfib v₀.1 v₀.2 _).mp (hy j)⟩
  have hzval : ∀ j, (z j).1
      = Fin.snoc v₀.1 ((fibFun hq hfib v₀).orderEmbOfFin (fibFun_card hq hfib v₀) j) :=
    fun j => rfl
  have hsec : ∀ j, (⟨Fin.init (z j).1, hS (z j).2⟩ : C) = v₀ := by
    intro j
    refine Subtype.ext ?_
    simp only [hzval j, Fin.init_snoc]
  have hex : ∀ j : Fin q, ∃ e : OpenPartialHomeomorph C S,
      (⟨Fin.init (z j).1, hS (z j).2⟩ : C) ∈ e.source ∧
        e (⟨Fin.init (z j).1, hS (z j).2⟩ : C) = z j ∧
        (∀ v ∈ e.source, (⟨Fin.init (e v).1, hS (e v).2⟩ : C) = v) := by
    -- the covering map is a local homeomorphism, so it has a local inverse through `z j`
    intro j
    have hf := hcov.isLocalHomeomorph
    refine ⟨hf.localInverseAt (z j), hf.apply_self_mem_localInverseAt_source, ?_, ?_⟩
    · exact hf.localInverseAt_apply_self
    · intro v hv
      have h1 : (hf.localInverseAt (z j)).symm ((hf.localInverseAt (z j)) v) = v :=
        OpenPartialHomeomorph.left_inv _ hv
      rwa [hf.localInverseAt_symm (z j)] at h1
  choose e he using hex
  let t : Fin q → C → ℝ := fun j v => (e j v).1 (Fin.last n)
  have hsrc : ∀ j, v₀ ∈ (e j).source := by
    intro j
    rw [← hsec j]
    exact (he j).1
  have htval : ∀ j, e j v₀ = z j := by
    intro j
    have h := (he j).2.1
    rwa [hsec j] at h
  have ht0 : ∀ j, t j v₀ = (fibFun hq hfib v₀).orderEmbOfFin (fibFun_card hq hfib v₀) j := by
    intro j
    simp only [t, htval j, hzval j, Fin.snoc_last]
  have hcont : ∀ j, ContinuousAt (t j) v₀ := by
    intro j
    have hc : ContinuousOn (t j) (e j).source := by
      have hproj : Continuous fun w : S => w.1 (Fin.last n) :=
        (continuous_apply (Fin.last n)).comp continuous_subtype_val
      exact hproj.comp_continuousOn (e j).continuousOn
    exact hc.continuousAt ((e j).open_source.mem_nhds (hsrc j))
  have hmem : ∀ᶠ v in nhds v₀, ∀ j, t j v ∈ fibFun hq hfib v := by
    have hsrc_all : ∀ᶠ v in nhds v₀, ∀ j, v ∈ (e j).source := by
      rw [Filter.eventually_all]
      intro j
      exact (e j).open_source.mem_nhds (hsrc j)
    filter_upwards [hsrc_all] with v hv
    intro j
    have h2 : (e j v).1 = Fin.snoc v.1 ((e j v).1 (Fin.last n)) :=
      section_eq_snoc hS (fun w hw => (he j).2.2 w hw) (hv j)
    refine (mem_fibFinset hq hfib v.1 v.2 _).mpr ?_
    rw [← h2]
    exact (e j v).2
  have hfin := eventually_orderEmbOfFin (F := fibFun hq hfib) (hcard := fibFun_card hq hfib)
    (x₀ := v₀) (e := t) hcont ht0 hmem
  have hcongr : t j =ᶠ[nhds v₀] (fun v : C => sect hq hfib j v.1) := by
    filter_upwards [hfin] with v hv
    rw [sect_eq hq hfib j v.1 v.2]
    simpa only [fibFun, fibFun_card] using hv j
  exact (hcont j).congr hcongr

/-! ## The main statement -/

theorem sections_of_covering {n q : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hq : 0 < q) (hS : S ⊆ {z | Fin.init z ∈ C})
    (hfib : ∀ x ∈ C, ({y : ℝ | Fin.snoc x y ∈ S}).ncard = q)
    (hcov : IsCoveringMap fun z : S => (⟨Fin.init z.1, hS z.2⟩ : C)) :
    ∃ s : Fin q → (Fin n → ℝ) → ℝ,
      (∀ j, ContinuousOn (s j) C) ∧
      (∀ x ∈ C, StrictMono fun j : Fin q => s j x) ∧
      (∀ j, ∀ x ∈ C, Fin.snoc x (s j x) ∈ S) ∧
      (∀ z ∈ S, ∃ j, z (Fin.last n) = s j (Fin.init z)) := by
  refine ⟨sect hq hfib, ?_, ?_, ?_, ?_⟩
  · intro j
    exact continuousOn_sect hq hS hfib hcov j
  · intro x hx
    exact strictMono_sect hq hfib x hx
  · intro j x hx
    exact sect_snoc_mem hq hfib j x hx
  · intro z hz
    exact exists_sect_eq hq hS hfib hz

end Work.WilE7
