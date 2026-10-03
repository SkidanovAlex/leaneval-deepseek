import Mathlib
import Submission.Work.OROneRel.hnnSplitAssembly
import Submission.Work.OROneRel.winRho_winRoot
import Submission.Work.OROneRel.winVertex_generation_of_pin
import Submission.Work.OROneRel.walking_telescope
import Submission.Work.OROneRel.conjugateHnnSubgroups_zInvariant
import Submission.Work.OROneRel.GaugeDefs

/-!
# The window splitting from the *pin*: the level data

This file develops the vocabulary of the *pin* that turns the explicit-inverse form of
`Work.OROneRel.magnusDomainDatum_of_windowInverse`
(`Submission/Work/OROneRel/hnnSplitAssembly.lean`) into a statement about the *level factors*
`mk (Wt j) * τ ^ (-j)` of the `Z`-cover:

* `winHd`/`winK` -- the vertex group `⟨winBeta | winRoot ^ l⟩` and its HNN extension;
* `winGammaWord` -- the **coedge word** of an edge `(x,i)` of the cover, in the free group on the
  window alphabet `β`: the generator attached to `(x,i)` when it is a *non-tree* edge of the window,
  and `1` when it is a tree edge (or lies outside the window);
* `winGammaK` -- its image in the HNN extension `K = HNNExtension ↥A ↥A ψ`;
* `levelEl` -- the **level element** `V j := of (Q j) * t ^ j` of a pin `Q : ℤ → winHd` with
  `θ (Q j) = mk (Wt j * τ ^ (-j))`;
* `genX` -- the **generator image** `X x := (V (i0 x))⁻¹ * Γ (x, i0 x) * V (i0 x + c x)`, where
  `i0 x` is a chosen level with `(x, i0 x)` an edge of the window.

The *content* of the pin is the consistency of the coedge labels at the different levels:

  `(V i)⁻¹ * Γ (x,i) * V (i + c x) = (V j)⁻¹ * Γ (x,j) * V (j + c x)`

for all window edges `(x,i)`, `(x,j)`, which is the hypothesis `hcons` of the theorem
`Work.OROneRel.magnusDomainDatum_of_pin` (below).  Given it, the step relations
`V i * X x = Γ (x,i) * V (i + c x)` hold at every window edge, and the telescoping identity
`Work.OROneRel.walking_telescope` along the walk of `Wt j` (whose traversals are tree edges of the
window, by `htree`) computes `FreeGroup.lift X (Wt j) = V j`, along the walk of `u` gives
`FreeGroup.lift X u = of (winRoot)` (whence `hXu`), and along the walk of `Wt 1` gives `hXτ`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The vertex group of the window**: `⟨winBeta | winRoot ^ l⟩`. -/
abbrev winHd (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) (l : ℕ) : Type u :=
  PresentedGroup ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
    Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))

/-- **The HNN extension of the vertex** over an associated subgroup `A` with the conjugation `ψ`. -/
abbrev winK {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} {l : ℕ}
    (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A) : Type u :=
  HNNExtension (winHd Wt c lo hi u l) A A ψ

/-- **The coedge word of an edge of the cover**: the generator of the window alphabet attached to
the non-tree edge `(x,i)`, and `1` if `(x,i)` is a tree edge of the window (or lies outside it). -/
noncomputable def winGammaWord (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : α × ℤ) :
    FreeGroup (Work.OROneRel.winBeta Wt c lo hi) :=
  (Work.OROneRel.winRootStep Wt c lo hi (p, true)).elim
    (1 : FreeGroup (Work.OROneRel.winBeta Wt c lo hi))
    (fun q => if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹)

/-- The coedge word of a *tree* edge of the window is `1`. -/
theorem winGammaWord_eq_one_of_tree {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {p : α × ℤ}
    (hp : p ∈ Work.OROneRel.winTree Wt c lo hi) : winGammaWord Wt c lo hi p = 1 := by
  classical
  have h1 : Work.OROneRel.coverClassAt Wt c p = 1 := (Work.OROneRel.mem_winTree.mp hp).2
  rw [winGammaWord, Work.OROneRel.winRootStep_none Wt c lo hi (p, true) h1]
  rfl

/-- The coedge word of a *non-tree* edge of the window is the corresponding generator. -/
theorem winGammaWord_eq_of_beta {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {p : α × ℤ}
    (hp : p ∈ Work.OROneRel.winE c lo hi) (hcl : Work.OROneRel.coverClassAt Wt c p ≠ 1) :
    winGammaWord Wt c lo hi p = FreeGroup.of (⟨p, hp, hcl⟩ : Work.OROneRel.winBeta Wt c lo hi) := by
  classical
  rw [winGammaWord, Work.OROneRel.winRootStep_of Wt c lo hi (p, true) hp hcl]
  rfl

/-- **The coedge element of the HNN extension.** -/
noncomputable def winGammaK (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A) (p : α × ℤ) : winK A ψ :=
  HNNExtension.of (PresentedGroup.mk
    ({Work.OROneRel.winRoot Wt c lo hi u ^ l} : Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
    (winGammaWord Wt c lo hi p))

/-- The coedge element of a *tree* edge is `1`. -/
theorem winGammaK_eq_one_of_tree {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    {l : ℕ} {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A} {p : α × ℤ}
    (hp : p ∈ Work.OROneRel.winTree Wt c lo hi) : winGammaK Wt c lo hi u l A ψ p = 1 := by
  rw [winGammaK, winGammaWord_eq_one_of_tree hp, map_one, map_one]

/-- The coedge element of a *non-tree* edge of the window is the corresponding vertex generator. -/
theorem winGammaK_eq_of_beta {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    {l : ℕ} {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A} {p : α × ℤ}
    (hp : p ∈ Work.OROneRel.winE c lo hi) (hcl : Work.OROneRel.coverClassAt Wt c p ≠ 1) :
    winGammaK Wt c lo hi u l A ψ p =
      HNNExtension.of (PresentedGroup.of (⟨p, hp, hcl⟩ : Work.OROneRel.winBeta Wt c lo hi)) := by
  rw [winGammaK, winGammaWord_eq_of_beta hp hcl]
  rfl

/-- **The level element of a pin**: `V j = of (Q j) * t ^ j`. -/
noncomputable def levelEl {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    {l : ℕ} {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A}
    (Q : ℤ → winHd Wt c lo hi u l) (j : ℤ) : winK A ψ :=
  HNNExtension.of (Q j) * HNNExtension.t ^ j

/-- **The generator image of the two-maps construction**, at a chosen window level of each
generator. -/
noncomputable def genX {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} {l : ℕ}
    {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A}
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l) (x : α) : winK A ψ :=
  (levelEl (A := A) (ψ := ψ) Q (Classical.choose (hcov x)))⁻¹ *
    winGammaK Wt c lo hi u l A ψ (x, Classical.choose (hcov x)) *
    levelEl (A := A) (ψ := ψ) Q (Classical.choose (hcov x) + c x)

/-- The chosen level of a generator is an edge of the window. -/
theorem genX_level_mem {c : α → ℤ} {lo hi : ℤ}
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi) (x : α) :
    (x, Classical.choose (hcov x)) ∈ Work.OROneRel.winE c lo hi :=
  Classical.choose_spec (hcov x)

/-- **The step relation of the two-maps construction.**  If the coedge labels are consistent along
the levels (`hcons`), then at every edge `(x,i)` of the window the level elements and the generator
image satisfy `V i * X x = Γ (x,i) * V (i + c x)`. -/
theorem levelEl_mul_genX {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} {l : ℕ}
    {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A}
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x))
    {x : α} {i : ℤ} (hmem : (x, i) ∈ Work.OROneRel.winE c lo hi) :
    levelEl (A := A) (ψ := ψ) Q i * genX (A := A) (ψ := ψ) hcov Q x =
      winGammaK Wt c lo hi u l A ψ (x, i) * levelEl (A := A) (ψ := ψ) Q (i + c x) := by
  have h := hcons x i (Classical.choose (hcov x)) hmem (genX_level_mem hcov x)
  rw [genX]
  rw [← h]
  group


/-! ## The telescoping along the tree paths

With the vocabulary above, the pin makes the comparison map invertible: the telescoping identity
`Work.OROneRel.walking_telescope` applied to the walk of `Wt j` (all of whose traversals are tree
edges of the window, by `htree`) computes `FreeGroup.lift X (Wt j) = V j`. -/

section Telescoping

variable {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} {l : ℕ}
  {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A}

/-- **The coedge product over a walk of tree edges is trivial.** -/
theorem winGammaK_prod_tree (L : List ((α × ℤ) × Bool))
    (hL : ∀ p ∈ L, p.1 ∈ Work.OROneRel.winTree Wt c lo hi) :
    (L.map (fun p => if p.2 then winGammaK Wt c lo hi u l A ψ p.1
      else (winGammaK Wt c lo hi u l A ψ p.1)⁻¹)).prod = 1 := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons, ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)),
      winGammaK_eq_one_of_tree (hL p (List.mem_cons_self ..))]
    cases p.2 <;> simp

/-- **The sign-corrected product over a decorated list is the product over the list.** -/
theorem decor_map_sign {M : Type*} [Group M] (f : α → M) (L : List (α × Bool)) (i : ℤ) :
    ((Work.OROneRel.decor c i L).map (fun p => if p.2 then f p.1.1 else (f p.1.1)⁻¹)).prod
      = (L.map (fun p => if p.2 then f p.1 else (f p.1)⁻¹)).prod := by
  induction L generalizing i with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b <;> simp only [Work.OROneRel.decor, List.map_cons, List.prod_cons,
      Bool.false_eq_true, if_true, if_false] <;>
      first
        | rw [ih (i - c a)]
        | rw [ih (i + c a)]

/-- The weight of the reduced word of an element is its cohomological weight. -/
theorem lsig_wordOf_eq (c : α → ℤ) (v : FreeGroup α) :
    Work.OROneRel.lsig c (Work.OROneRel.wordOf v) = (Work.OROneRel.cohom c v).toAdd := by
  have h : Work.OROneRel.cohom c v = Multiplicative.ofAdd
      (Work.OROneRel.lsig c (Work.OROneRel.wordOf v)) := by
    rw [← Work.OROneRel.cohom_mk c (Work.OROneRel.wordOf v), Work.OROneRel.mk_wordOf]
  exact (congrArg Multiplicative.toAdd h).symm

/-- **The telescoping along a tree path.**  If the coedge labels are consistent along the levels and
`Q 0 = 1`, then the value of the comparison map on the tree path word `Wt j` is the level element
`V j`. -/
theorem lift_genX_eq_levelEl (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l) (hQ0 : Q 0 = 1)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x))
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    {j : ℤ} (hlj : lo ≤ j) (hjh : j ≤ hi) :
    FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (Wt j) = levelEl (A := A) (ψ := ψ) Q j := by
  classical
  set L : List ((α × ℤ) × Bool) := Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt j)) with hL
  have hstep : ∀ p ∈ L, levelEl (A := A) (ψ := ψ) Q p.1.2 * genX (A := A) (ψ := ψ) hcov Q p.1.1 =
      winGammaK Wt c lo hi u l A ψ p.1 * levelEl (A := A) (ψ := ψ) Q (p.1.2 + c p.1.1) := by
    intro p hp
    have htw : Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi :=
      htree j hlj hjh p (hL ▸ hp)
    have hW : p.1 ∈ Work.OROneRel.winE c lo hi := (Work.OROneRel.mem_winTree.mp htw).1
    exact levelEl_mul_genX (A := A) (ψ := ψ) hcov Q hcons hW
  have ht := Work.OROneRel.walking_telescope (K := winK A ψ) c (fun x => genX (A := A) (ψ := ψ) hcov Q x)
    (fun i => levelEl (A := A) (ψ := ψ) Q i) (fun e => winGammaK Wt c lo hi u l A ψ e)
    (Work.OROneRel.wordOf (Wt j)) 0 hstep
  -- the two products
  have hPX : (L.map (fun p => if p.2 then genX (A := A) (ψ := ψ) hcov Q p.1.1
      else (genX (A := A) (ψ := ψ) hcov Q p.1.1)⁻¹)).prod =
      FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (Wt j) := by
    rw [hL, decor_map_sign (genX (A := A) (ψ := ψ) hcov Q) (Work.OROneRel.wordOf (Wt j)) 0]
    conv_rhs => rw [← Work.OROneRel.mk_wordOf (Wt j)]
    rw [FreeGroup.lift_mk]
    congr 1
    refine List.map_congr_left (fun p hp => ?_)
    obtain ⟨a, b⟩ := p
    cases b <;> rfl
  have hPG : (L.map (fun p => if p.2 then winGammaK Wt c lo hi u l A ψ p.1
      else (winGammaK Wt c lo hi u l A ψ p.1)⁻¹)).prod = 1 :=
    winGammaK_prod_tree L (fun p hp => htree j hlj hjh p (hL ▸ hp))
  have hlsig : Work.OROneRel.lsig c (Work.OROneRel.wordOf (Wt j)) = j := by
    rw [lsig_wordOf_eq, hcoh j]
    rfl
  have hV0 : levelEl (A := A) (ψ := ψ) Q 0 = 1 := by
    rw [levelEl, hQ0, map_one, zpow_zero, mul_one]
  rw [hPG, hPX, hlsig, hV0, one_mul, one_mul, zero_add] at ht
  exact ht

/-- **The coedge condition of the two-maps construction, from the pin.** -/
theorem lift_genX_coverClassAt (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l) (hQ0 : Q 0 = 1)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x))
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (e : Work.OROneRel.winBeta Wt c lo hi) :
    FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (Work.OROneRel.coverClassAt Wt c e.1) =
      HNNExtension.of (PresentedGroup.of e) := by
  classical
  obtain ⟨⟨x, i⟩, hm, hcl⟩ := e
  obtain ⟨h1, h2, h3, h4⟩ := Work.OROneRel.mem_winE.mp hm
  have hxi := lift_genX_eq_levelEl (A := A) (ψ := ψ) hcov Q hQ0 hcons hcoh htree h1 h2
  have hxj := lift_genX_eq_levelEl (A := A) (ψ := ψ) hcov Q hQ0 hcons hcoh htree h3 h4
  have hstep := levelEl_mul_genX (A := A) (ψ := ψ) hcov Q hcons hm
  have hcc : Work.OROneRel.coverClassAt Wt c (x, i) =
      Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹ := gaugeMap_of Wt c (x, i)
  conv_lhs => rw [hcc]
  rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, hxi, hxj]
  rw [hstep, mul_assoc, mul_inv_cancel, mul_one, winGammaK_eq_of_beta hm hcl]
  exact congrArg (fun q : Work.OROneRel.winBeta Wt c lo hi =>
    HNNExtension.of (PresentedGroup.of q)) (Subtype.ext rfl)

/-- **The tracking condition of the two-maps construction, from the pin**, with the stable letter
`τ := Wt 1`. -/
theorem lift_genX_Wt_one (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l) (hQ0 : Q 0 = 1) (hQ1 : Q 1 = 1)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x))
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hl1 : lo ≤ 1) (hh1 : 1 ≤ hi) :
    FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (Wt 1) = HNNExtension.t := by
  rw [lift_genX_eq_levelEl (A := A) (ψ := ψ) hcov Q hQ0 hcons hcoh htree hl1 hh1, levelEl, hQ1,
    map_one, one_mul, zpow_one]

end Telescoping

end Work.OROneRel