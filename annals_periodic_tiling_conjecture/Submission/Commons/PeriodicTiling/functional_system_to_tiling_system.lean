import Mathlib
import Submission.Commons.PeriodicTiling.IsAperiodicTilingEquation_map_addEquiv

open scoped Pointwise

namespace Commons.PeriodicTiling

noncomputable section

/-- The notation `a + E`, for `a : H` and `E : Set H`, means `{a} + E`.
This instance makes the statements of functional equations readable in the same way
as in the paper. -/
instance elementAddSet {H : Type*} [Add H] : HAdd H (Set H) (Set H) :=
  ⟨fun a s => ({a} : Set H) + s⟩

/-- The vertical line tile `{0} × H` in `G × H`. -/
def vertTile (G : Type*) [Zero G] (H : Type*) : Set (G × H) :=
  {p | p.1 = 0}

/-- The graph of a function `α : G → H`. -/
def graph {G : Type*} {H : Type*} (α : G → H) : Set (G × H) :=
  {p | p.2 = α p.1}

/-- The finite tile associated to the functional equation with shifts `h` and sets `E`. -/
def funcTile {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {M : ℕ} (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H) (i : Fin M) : Set (G × H) :=
  ⋃ j : Fin (J i), (fun e : H => (- h i j, e)) '' E i j

/-- If `A` tiles with the vertical line tile, then `A` is a graph.  This is the function
whose graph is `A`. -/
def graphFun {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {A : Set (G × H)} (h : IsTiling (vertTile G H) A) : G → H :=
  fun x => (Classical.choose (h.existsUnique (x, 0)).exists).1.1.2

lemma vertTile_finite {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H] [Finite H] :
    (vertTile G H).Finite := by
  have hfin : ((fun h : H => ((0 : G), h)) '' Set.univ).Finite :=
    (Set.finite_univ.image _)
  refine hfin.subset ?_
  intro p hp
  refine ⟨p.2, by simp, ?_⟩
  ext
  · simpa [vertTile] using hp.symm
  · rfl

lemma vertTile_nonempty (G : Type*) [Zero G] (H : Type*) [Zero H] :
    (vertTile G H).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp [vertTile]

lemma funcTile_finite {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H] [Finite H]
    {M : ℕ} (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H) (i : Fin M) :
    (funcTile J h E i).Finite := by
  classical
  have hfin : (⋃ j : Fin (J i), (fun e : H => (- h i j, e)) '' E i j).Finite := by
    apply Set.finite_iUnion
    intro j
    exact (E i j).toFinite.image _
  simpa [funcTile] using hfin

lemma funcTile_nonempty {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {M : ℕ} (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H)
    (hE : ∀ i j, (E i j).Nonempty) (α : G → H)
    (hα : ∀ i x y, ∃ j : Fin (J i), y ∈ α (x + h i j) + E i j) (i : Fin M) :
    (funcTile J h E i).Nonempty := by
  classical
  obtain ⟨j, _⟩ := hα i 0 0
  obtain ⟨e, he⟩ := hE i j
  refine ⟨(- h i j, e), ?_⟩
  change (-h i j, e) ∈ ⋃ j : Fin (J i), (fun e : H => (- h i j, e)) '' E i j
  rw [Set.mem_iUnion]
  exact ⟨j, (Set.mem_image (fun e : H => (- h i j, e)) (E i j) (-h i j, e)).mpr ⟨e, he, rfl⟩⟩

lemma graph_tiling_vertical {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    (α : G → H) : IsTiling (vertTile G H) (graph α) := by
  change AddSubgroup.IsComplement (graph α) (vertTile G H)
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro z
  let a : graph α := ⟨(z.1, α z.1), by simp [graph]⟩
  let f : vertTile G H := ⟨(0, z.2 - α z.1), by simp [vertTile]⟩
  refine ⟨(a, f), ?_, ?_⟩
  · ext <;> simp [a, f, add_sub_cancel]
  · intro y hy
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · have hfst : y.2.1.1 = 0 := y.2.2
        have := congrArg Prod.fst hy
        simpa [hfst] using this
      · have hfst : y.2.1.1 = 0 := y.2.2
        have hfirst : y.1.1.1 = z.1 := by
          have := congrArg Prod.fst hy
          simpa [hfst] using this
        have hp : (y.1 : graph α).1.2 = α (y.1 : graph α).1.1 := y.1.property
        have hy1 : y.1.1.2 = α z.1 := by
          simpa [graph, hfirst] using hp
        exact hy1
    · apply Subtype.ext
      apply Prod.ext
      · exact y.2.2
      · have hfst : y.2.1.1 = 0 := y.2.2
        have := congrArg Prod.fst hy
        have hfirst : y.1.1.1 = z.1 := by simpa [hfst] using this
        have hp : (y.1 : graph α).1.2 = α (y.1 : graph α).1.1 := y.1.property
        have hy1 : y.1.1.2 = α z.1 := by
          simpa [graph, hfirst] using hp
        have hsecond := congrArg Prod.snd hy
        have hy_sum : y.1.1.2 + y.2.1.2 = z.2 := by
          simpa using hsecond
        calc
          y.2.1.2 = - α z.1 + (α z.1 + y.2.1.2) := by simp
          _ = - α z.1 + z.2 := by rw [← hy1, hy_sum]
          _ = z.2 - α z.1 := by abel

lemma graphFun_mem {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {A : Set (G × H)} (h : IsTiling (vertTile G H) A) (x : G) :
    (x, graphFun h x) ∈ A := by
  let p := Classical.choose (h.existsUnique (x, 0)).exists
  have hp : p.1.1 + p.2.1 = (x, 0) := Classical.choose_spec (h.existsUnique (x, 0)).exists
  have hp2 : p.2.1.1 = 0 := p.2.2
  have hp1 : p.1.1.1 = x := by
    have := congrArg Prod.fst hp
    simpa [hp2] using this
  have hp_eq : (x, graphFun h x) = (p.1 : G × H) := by
    ext
    · simpa [graphFun, hp1] using hp1.symm
    · rfl
  rw [hp_eq]
  exact p.1.2

lemma graphFun_eq_of_mem {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {A : Set (G × H)} (h : IsTiling (vertTile G H) A)
    {x : G} {y : H} (hy : (x, y) ∈ A) : graphFun h x = y := by
  let p := Classical.choose (h.existsUnique (x, 0)).exists
  have hp : p.1.1 + p.2.1 = (x, 0) := Classical.choose_spec (h.existsUnique (x, 0)).exists
  have hp2 : p.2.1.1 = 0 := p.2.2
  have hp1 : p.1.1.1 = x := by
    have := congrArg Prod.fst hp
    simpa [hp2] using this
  let a : A := ⟨(x, y), hy⟩
  let f : vertTile G H := ⟨(0, -y), by simp [vertTile]⟩
  have hsum : (a : G × H) + (f : G × H) = (x, 0) := by
    ext <;> simp [a, f]
  have hpair : (a, f) = p := (h.existsUnique (x, 0)).unique hsum hp
  have ha : a = p.1 := congrArg Prod.fst hpair
  have hy_eq : y = (p.1 : G × H).2 := by
    have := congrArg (fun t : A => (t : G × H).2) ha
    simpa [a] using this
  change (p.1 : G × H).2 = y
  exact hy_eq.symm

lemma graph_eq_of_vertical_tiling {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {A : Set (G × H)} (h : IsTiling (vertTile G H) A) :
    A = graph (graphFun h) := by
  ext p
  constructor
  · intro hp
    have hx := graphFun_eq_of_mem h hp
    simp [graph, hx]
  · intro hp
    have hm := graphFun_mem h p.1
    have hp' : (p.1, graphFun h p.1) = p := by
      ext
      · rfl
      · exact hp.symm
    simpa [hp'] using hm

lemma graph_tiling_funcTile {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {M : ℕ} (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H) (i : Fin M) (α : G → H)
    (hα : ∀ x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j) :
    IsTiling (funcTile J h E i) (graph α) := by
  change AddSubgroup.IsComplement (graph α) (funcTile J h E i)
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro z
  obtain ⟨j, hj⟩ := (hα z.1 z.2).exists
  rcases (Set.mem_add.mp hj) with ⟨a, ha, e, he, hae⟩
  have ha' : a = α (z.1 + h i j) := by simpa using ha
  have hy : z.2 = α (z.1 + h i j) + e := by
    simpa [ha'] using hae.symm
  let a_p : graph α := ⟨(z.1 + h i j, α (z.1 + h i j)), by simp [graph]⟩
  let f_p : funcTile J h E i := ⟨(- h i j, e), by
    change (-h i j, e) ∈ ⋃ j : Fin (J i), (fun e : H => (- h i j, e)) '' E i j
    rw [Set.mem_iUnion]
    exact ⟨j, (Set.mem_image (fun e : H => (- h i j, e)) (E i j) (-h i j, e)).mpr ⟨e, he, rfl⟩⟩⟩
  refine ⟨(a_p, f_p), ?_, ?_⟩
  · ext <;> simp [a_p, f_p, hy]
  · intro y hsum
    rcases (Set.mem_iUnion.mp y.2.2) with ⟨j', hfj'⟩
    rcases ((Set.mem_image (fun e : H => (- h i j', e)) (E i j') y.2.1).mp hfj') with ⟨e', he', hfeq⟩
    have hfirst : y.1.1.1 + (- h i j') = z.1 := by
      have := congrArg Prod.fst hsum
      simpa [← hfeq] using this
    have ha1 : y.1.1.1 = z.1 + h i j' := by
      have := congrArg (fun t : G => t + h i j') hfirst
      simpa [add_assoc, add_comm, add_left_comm] using this
    have ha2 : y.1.1.2 = α (z.1 + h i j') := by
      have hp : (y.1 : graph α).1.2 = α (y.1 : graph α).1.1 := y.1.property
      simpa [graph, ha1] using hp
    have hsecond : y.1.1.2 + e' = z.2 := by
      have := congrArg Prod.snd hsum
      simpa [← hfeq] using this
    have hj'_mem : z.2 ∈ α (z.1 + h i j') + E i j' := by
      change z.2 ∈ ({α (z.1 + h i j')} : Set H) + E i j'
      rw [Set.mem_add]
      refine ⟨α (z.1 + h i j'), by simp, e', he', ?_⟩
      simpa [ha2] using hsecond
    have hj_eq : j' = j := (hα z.1 z.2).unique hj'_mem hj
    subst j'
    have he_eq : e' = e := by
      have hsecond' : α (z.1 + h i j) + e' = z.2 := by simpa [ha2] using hsecond
      have hcancel : α (z.1 + h i j) + e' = α (z.1 + h i j) + e := by
        simpa [hy] using hsecond'
      exact add_left_cancel hcancel
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · simpa [a_p, ha1] using ha1
      · have ha2j : y.1.1.2 = α (z.1 + h i j) := by simpa [ha2]
        simpa [a_p, ha2j] using ha2j
    · apply Subtype.ext
      apply Prod.ext
      · have hy2_fst : (y.2 : G × H).1 = -h i j := by
          simpa using congrArg Prod.fst hfeq.symm
        simpa [f_p] using hy2_fst
      · have hy2_snd : (y.2 : G × H).2 = e := by
          have hsnd := congrArg Prod.snd hfeq.symm
          simpa [he_eq] using hsnd
        simpa [f_p] using hy2_snd

lemma eq_of_pair_mem_of_solution {G : Type*} [AddCommGroup G]
    {H : Type*} [AddCommGroup H]
    {M : ℕ} (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H)
    (hsol : ∃ α : G → H, ∀ i x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j)
    {i : Fin M} {j k : Fin (J i)} (hg : h i j = h i k)
    {e : H} (hej : e ∈ E i j) (hek : e ∈ E i k) : j = k := by
  rcases hsol with ⟨α0, hα0⟩
  have hmemj : α0 (h i j) + e ∈ α0 (0 + h i j) + E i j := by
    rw [zero_add]
    change α0 (h i j) + e ∈ ({α0 (h i j)} : Set H) + E i j
    rw [Set.mem_add]
    exact ⟨α0 (h i j), by simp, e, hej, rfl⟩
  have hmemk : α0 (h i j) + e ∈ α0 (0 + h i k) + E i k := by
    rw [zero_add]
    change α0 (h i j) + e ∈ ({α0 (h i k)} : Set H) + E i k
    rw [Set.mem_add]
    refine ⟨α0 (h i k), by simp, e, hek, ?_⟩
    rw [← hg]
  exact (hα0 i 0 (α0 (h i j) + e)).unique hmemj hmemk

lemma functional_of_graph_tiling {G : Type*} [AddCommGroup G]
    {H : Type*} [AddCommGroup H]
    {M : ℕ} (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H)
    (hsol : ∃ α : G → H, ∀ i x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j)
    (i : Fin M) (α : G → H)
    (ht : IsTiling (funcTile J h E i) (graph α)) :
    ∀ x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j := by
  intro x y
  have hex : ∃ j : Fin (J i), y ∈ α (x + h i j) + E i j := by
    obtain ⟨p, hp⟩ := (ht.existsUnique (x, y))
    have hsum : p.1.1 + p.2.1 = (x, y) := hp.1
    rcases (Set.mem_iUnion.mp p.2.2) with ⟨j, hfj⟩
    rcases ((Set.mem_image (fun e : H => (- h i j, e)) (E i j) p.2.1).mp hfj) with ⟨e, he, hfeq⟩
    have hfirst : p.1.1.1 + (- h i j) = x := by
      have := congrArg Prod.fst hsum
      simpa [← hfeq] using this
    have ha1 : p.1.1.1 = x + h i j := by
      have := congrArg (fun t : G => t + h i j) hfirst
      simpa [add_assoc, add_comm, add_left_comm] using this
    have hpα : p.1.1.2 = α p.1.1.1 := by
      change (p.1 : graph α).1.2 = α (p.1 : graph α).1.1
      exact p.1.property
    have hsecond : p.1.1.2 + e = y := by
      have := congrArg Prod.snd hsum
      simpa [← hfeq] using this
    refine ⟨j, ?_⟩
    change y ∈ ({α (x + h i j)} : Set H) + E i j
    rw [Set.mem_add]
    refine ⟨α (x + h i j), by simp, e, he, ?_⟩
    simpa [ha1, hpα] using hsecond
  refine ⟨hex.choose, hex.choose_spec, ?_⟩
  intro k hk
  have get_e : ∀ j : Fin (J i), y ∈ α (x + h i j) + E i j →
      ∃ e : H, e ∈ E i j ∧ α (x + h i j) + e = y := by
    intro j hj
    change y ∈ ({α (x + h i j)} : Set H) + E i j at hj
    rcases (Set.mem_add.mp hj) with ⟨a, ha, e, he, hae⟩
    have ha' : a = α (x + h i j) := by simpa using ha
    exact ⟨e, he, by simpa [ha'] using hae⟩
  have hchoose := hex.choose_spec
  rcases get_e hex.choose hchoose with ⟨e1, he1, hy1⟩
  rcases get_e k hk with ⟨e2, he2, hy2⟩
  let a1 : graph α := ⟨(x + h i hex.choose, α (x + h i hex.choose)), by simp [graph]⟩
  let f1 : funcTile J h E i := ⟨(- h i hex.choose, e1), by
    change (-h i hex.choose, e1) ∈ ⋃ j : Fin (J i), (fun e : H => (- h i j, e)) '' E i j
    rw [Set.mem_iUnion]
    exact ⟨hex.choose, (Set.mem_image (fun e : H => (- h i hex.choose, e)) (E i hex.choose) (-h i hex.choose, e1)).mpr ⟨e1, he1, rfl⟩⟩⟩
  let a2 : graph α := ⟨(x + h i k, α (x + h i k)), by simp [graph]⟩
  let f2 : funcTile J h E i := ⟨(- h i k, e2), by
    change (-h i k, e2) ∈ ⋃ j : Fin (J i), (fun e : H => (- h i j, e)) '' E i j
    rw [Set.mem_iUnion]
    exact ⟨k, (Set.mem_image (fun e : H => (- h i k, e)) (E i k) (-h i k, e2)).mpr ⟨e2, he2, rfl⟩⟩⟩
  have hsum1 : (a1 : G × H) + (f1 : G × H) = (x, y) := by
    ext <;> simp [a1, f1, hy1]
  have hsum2 : (a2 : G × H) + (f2 : G × H) = (x, y) := by
    ext <;> simp [a2, f2, hy2]
  have hpair : (a1, f1) = (a2, f2) := (ht.existsUnique (x, y)).unique hsum1 hsum2
  have hf : f1 = f2 := congrArg Prod.snd hpair
  have hf_eq : (- h i hex.choose, e1) = (- h i k, e2) := by
    exact congrArg Subtype.val hf
  have hg : h i hex.choose = h i k := by
    have := congrArg Prod.fst hf_eq
    simpa using this
  have he_eq : e1 = e2 := by
    have := congrArg Prod.snd hf_eq
    simpa using this
  have he2' : e1 ∈ E i k := by
    simpa [he_eq] using he2
  exact (@eq_of_pair_mem_of_solution G _ H _ M J h E hsol i hex.choose k hg e1 he1 he2').symm

lemma graph_periodic_of_periodic {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H]
    {A : Set (G × H)} (α : G → H) (hgraph : A = graph α) (hA : IsPeriodicTilingSet A) :
    ∃ L : AddSubgroup G, L.FiniteIndex ∧ ∀ x : G, ∀ g : G, g ∈ L → α (x + g) = α x := by
  rcases hA with ⟨L, hLfin, s, hAeq⟩
  let φ : G →+ G × H := (AddMonoidHom.id G).prod 0
  let K : AddSubgroup G := AddSubgroup.comap φ L
  have hKfin : K.FiniteIndex := by
    let q : (G × H) →+ (G × H) ⧸ L := QuotientAddGroup.mk' L
    let ψ : G →+ (G × H) ⧸ L := q.comp φ
    haveI : L.FiniteIndex := hLfin
    haveI : Finite ((G × H) ⧸ L) := AddSubgroup.finite_quotient_of_finiteIndex (H := L)
    have hψker : ψ.ker = K := by
      ext g
      rw [AddMonoidHom.mem_ker]
      change q (g, 0) = 0 ↔ (g, 0) ∈ L
      rw [QuotientAddGroup.mk'_apply]
      change QuotientAddGroup.mk (s := L) (g, 0) = QuotientAddGroup.mk (s := L) (0, 0) ↔ (g, 0) ∈ L
      rw [QuotientAddGroup.eq]
      constructor
      · intro h
        have h' : -(-(g, 0)) ∈ L := AddSubgroup.neg_mem L (by simpa using h)
        simpa using h'
      · intro h
        simpa using AddSubgroup.neg_mem L h
    have hψfin : ψ.ker.FiniteIndex := AddSubgroup.finiteIndex_ker ψ
    simpa [hψker] using hψfin
  refine ⟨K, hKfin, ?_⟩
  intro x g hg
  have hgL : (g, 0) ∈ L := by
    simpa [K, φ] using hg
  have hxA : (x, α x) ∈ A := by
    rw [hgraph]
    simp [graph]
  have hxA_add : (x + g, α x) ∈ A := by
    have hxA' : (x, α x) ∈ (s : Set (G × H)) + L := by
      simpa [hAeq] using hxA
    rcases (Set.mem_add.mp hxA') with ⟨a, ha, l, hl, hsum⟩
    have hsum' : a + l = (x, α x) := hsum
    have hsum_new : a + (l + (g, 0)) = (x + g, α x) := by
      rw [← add_assoc, hsum']
      ext <;> simp [add_assoc, add_comm, add_left_comm]
    have hmemL : l + (g, 0) ∈ L := AddSubgroup.add_mem L hl hgL
    have : (x + g, α x) ∈ (s : Set (G × H)) + L := by
      rw [Set.mem_add]
      exact ⟨a, ha, l + (g, 0), hmemL, hsum_new⟩
    simpa [hAeq] using this
  have hxAgraph : (x + g, α x) ∈ graph α := by
    simpa [hgraph] using hxA_add
  simpa [graph] using hxAgraph.symm

theorem functional_system_to_tiling_system
    {G : Type*} [AddCommGroup G]
    {H : Type*} [AddCommGroup H] [Finite H]
    {M : ℕ} (J : Fin M → ℕ)
    (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H)
    (hE : ∀ i j, (E i j).Nonempty)
    (hsol : ∃ α : G → H, ∀ i x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j)
    (haper : ∀ α : G → H,
      (∀ i x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j) →
      ¬ ∃ L : AddSubgroup G, L.FiniteIndex ∧
        ∀ x : G, ∀ g : G, g ∈ L → α (x + g) = α x) :
    ∃ M' : ℕ, ∃ F : Fin M' → Set (G × H),
      (∀ i : Fin M', (F i).Finite ∧ (F i).Nonempty) ∧
      (∃ A : Set (G × H), ∀ i : Fin M', IsTiling (F i) A) ∧
      ∀ A : Set (G × H), (∀ i : Fin M', IsTiling (F i) A) → ¬ IsPeriodicTilingSet A := by
  classical
  have hsol' := hsol
  obtain ⟨α, hα⟩ := hsol
  let F0 : Fin M → Set (G × H) := fun i => funcTile J h E i
  let F : Fin (M + 1) → Set (G × H) := Fin.snoc F0 (vertTile G H)
  refine ⟨M + 1, F, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last =>
        simp [F, F0]
        exact ⟨vertTile_finite, vertTile_nonempty G H⟩
    | cast i =>
        simp [F, F0]
        exact ⟨funcTile_finite J h E i, funcTile_nonempty J h E hE α (fun i x y => (hα i x y).exists) i⟩
  · refine ⟨graph α, ?_⟩
    intro i
    cases i using Fin.lastCases with
    | last =>
        simpa [F, F0] using graph_tiling_vertical α
    | cast i =>
        simpa [F, F0] using graph_tiling_funcTile J h E i α (hα i)
  · intro A htil hAper
    have hvert : IsTiling (vertTile G H) A := by
      simpa [F, F0] using htil (Fin.last M)
    let β : G → H := graphFun hvert
    have hgraph : A = graph β := graph_eq_of_vertical_tiling hvert
    have hβsol : ∀ i x y, ∃! j : Fin (J i), y ∈ β (x + h i j) + E i j := by
      intro i x y
      have ht_i : IsTiling (funcTile J h E i) (graph β) := by
        simpa [F, F0, hgraph] using htil (Fin.castSucc i)
      exact functional_of_graph_tiling J h E hsol' i β ht_i x y
    have hβaper := haper β hβsol
    have hβperiodic : ∃ L : AddSubgroup G, L.FiniteIndex ∧
        ∀ x : G, ∀ g : G, g ∈ L → β (x + g) = β x :=
      graph_periodic_of_periodic β hgraph hAper
    exact hβaper hβperiodic

end

end Commons.PeriodicTiling

