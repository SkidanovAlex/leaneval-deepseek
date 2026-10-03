import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.WallGraph
import Submission.Work.HornSC.CellBoundaryJordan.WallCycle.Defs

/-!
# Evenness of the degree of the wall-dart graph

`wallDartGraph A` is the graph on the lattice points whose darts are the oriented wall steps of
`A` (`wallDarts A = wallStepFinset A ∪ (wallStepFinset A).swap`).  Its darts from a point `a` are
exactly the four unit wall steps of `A` incident with `a`, and the local lemma `wall_local_even`
says that the number of wall segments through a lattice point is always even.

We prove `Even (DartGraph.deg (wallDartGraph A) a)` by identifying the degree with `WallDeg A a`
(the number of wall edges incident with `a`, from `WallCycle.Defs`), whose evenness is
`WallCycle.even_WallDeg`.
-/

namespace Work.HornSC.CellBoundaryJordan

open WallCycle

/-! ## Membership of a directed pair in the wall-step set -/

/-- Membership of a (directed) *pair* in `wallStepFinset A`: it is an east step from its first
point, or a north step from its first point. -/
lemma mem_wallStepFinset_pair {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} :
    ((u, v) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallStepFinset A ↔
      (hWallAt A u ∧ v = (u.1 + 1, u.2)) ∨ (vWallAt A u ∧ v = (u.1, u.2 + 1)) := by
  rw [mem_wallStepFinset]
  constructor
  · rintro (⟨w, hw, he⟩ | ⟨w, hw, he⟩)
    · left
      have h1 : u = w := congrArg Prod.fst he
      have h2 : v = (w.1 + 1, w.2) := congrArg Prod.snd he
      exact ⟨by rwa [h1], by rw [h2, h1]⟩
    · right
      have h1 : u = w := congrArg Prod.fst he
      have h2 : v = (w.1, w.2 + 1) := congrArg Prod.snd he
      exact ⟨by rwa [h1], by rw [h2, h1]⟩
  · rintro (⟨hw, hv⟩ | ⟨hw, hv⟩)
    · exact Or.inl ⟨u, hw, by rw [hv]⟩
    · exact Or.inr ⟨u, hw, by rw [hv]⟩

/-! ## Membership of the four unit darts leaving a point -/

lemma dart_east (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    ((u, (u.1 + 1, u.2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallDarts A ↔ hWallAt A u := by
  rw [mem_wallDarts]
  have hswap : ((u, (u.1 + 1, u.2)) : (ℤ × ℤ) × (ℤ × ℤ)).swap = ((u.1 + 1, u.2), u) := rfl
  rw [hswap, mem_wallStepFinset_pair, mem_wallStepFinset_pair]
  constructor
  · rintro ((⟨h, -⟩ | ⟨-, ha⟩) | (⟨-, hb⟩ | ⟨-, hc⟩))
    · exact h
    · have ha' : u.1 + 1 = u.1 := congrArg Prod.fst ha
      omega
    · have hb' : u.1 = u.1 + 1 + 1 := congrArg Prod.fst hb
      omega
    · have hc' : u.2 = u.2 + 1 := congrArg Prod.snd hc
      omega
  · intro h; exact Or.inl (Or.inl ⟨h, rfl⟩)

lemma dart_west (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    ((u, (u.1 - 1, u.2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallDarts A ↔ hWallAt A (u.1 - 1, u.2) := by
  rw [mem_wallDarts]
  have hswap : ((u, (u.1 - 1, u.2)) : (ℤ × ℤ) × (ℤ × ℤ)).swap = ((u.1 - 1, u.2), u) := rfl
  rw [hswap, mem_wallStepFinset_pair, mem_wallStepFinset_pair]
  constructor
  · rintro ((⟨-, ha⟩ | ⟨-, hb⟩) | (⟨h, -⟩ | ⟨-, hc⟩))
    · have ha' : u.1 - 1 = u.1 + 1 := congrArg Prod.fst ha
      omega
    · have hb' : u.1 - 1 = u.1 := congrArg Prod.fst hb
      omega
    · exact h
    · have hc' : u.2 = u.2 + 1 := congrArg Prod.snd hc
      omega
  · intro h
    refine Or.inr (Or.inl ⟨h, ?_⟩)
    ext <;> omega

lemma dart_north (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    ((u, (u.1, u.2 + 1)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallDarts A ↔ vWallAt A u := by
  rw [mem_wallDarts]
  have hswap : ((u, (u.1, u.2 + 1)) : (ℤ × ℤ) × (ℤ × ℤ)).swap = ((u.1, u.2 + 1), u) := rfl
  rw [hswap, mem_wallStepFinset_pair, mem_wallStepFinset_pair]
  constructor
  · rintro ((⟨-, ha⟩ | ⟨h, -⟩) | (⟨-, hb⟩ | ⟨-, hc⟩))
    · have ha' : u.2 + 1 = u.2 := congrArg Prod.snd ha
      omega
    · exact h
    · have hb' : u.1 = u.1 + 1 := congrArg Prod.fst hb
      omega
    · have hc' : u.2 = u.2 + 1 + 1 := congrArg Prod.snd hc
      omega
  · intro h; exact Or.inl (Or.inr ⟨h, rfl⟩)

lemma dart_south (A : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    ((u, (u.1, u.2 - 1)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallDarts A ↔ vWallAt A (u.1, u.2 - 1) := by
  rw [mem_wallDarts]
  have hswap : ((u, (u.1, u.2 - 1)) : (ℤ × ℤ) × (ℤ × ℤ)).swap = ((u.1, u.2 - 1), u) := rfl
  rw [hswap, mem_wallStepFinset_pair, mem_wallStepFinset_pair]
  constructor
  · rintro ((⟨-, ha⟩ | ⟨-, hb⟩) | (⟨-, hc⟩ | ⟨h, -⟩))
    · have ha' : u.1 = u.1 + 1 := congrArg Prod.fst ha
      omega
    · have hb' : u.2 - 1 = u.2 + 1 := congrArg Prod.snd hb
      omega
    · have hc' : u.1 = u.1 + 1 := congrArg Prod.fst hc
      omega
    · exact h
  · intro h
    refine Or.inr (Or.inr ⟨h, ?_⟩)
    ext <;> omega

/-! ## The general membership characterization -/

/-- A directed pair lies in `wallDarts A` exactly when its segment is a wall of `A` incident with
its first point. -/
lemma mem_wallDarts_pair (A : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    ((u, v) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallDarts A ↔ WallAdj A u v := by
  constructor
  · intro h
    have hiu : IsUnitAdj u v := wallDarts_isUnitAdj h
    rcases hiu with h1 | h1 | h1 | h1
    · subst h1; exact (WallAdj_east A u).mpr ((dart_east A u).mp h)
    · subst h1; exact (WallAdj_west A u).mpr ((dart_west A u).mp h)
    · subst h1; exact (WallAdj_north A u).mpr ((dart_north A u).mp h)
    · subst h1; exact (WallAdj_south A u).mpr ((dart_south A u).mp h)
  · intro h
    have hiu : IsUnitAdj u v := WallAdj_unitAdj h
    rcases hiu with h1 | h1 | h1 | h1
    · subst h1; exact (dart_east A u).mpr ((WallAdj_east A u).mp h)
    · subst h1; exact (dart_west A u).mpr ((WallAdj_west A u).mp h)
    · subst h1; exact (dart_north A u).mpr ((WallAdj_north A u).mp h)
    · subst h1; exact (dart_south A u).mpr ((WallAdj_south A u).mp h)

/-! ## The degree is the number of incident wall edges -/

lemma deg_eq_WallDeg (A : Finset (ℤ × ℤ)) (a : ℤ × ℤ) :
    DartGraph.deg (wallDartGraph A) a = WallDeg A a := by
  have himg : (wallDarts A).filter (fun e => e.1 = a) =
      ((nbhdPts a).filter (fun w => WallAdj A a w)).image (fun w => (a, w)) := by
    ext e
    obtain ⟨p, q⟩ := e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨he, hp⟩
      have h' : ((a, q) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ wallDarts A := by
        rw [hp] at he; exact he
      have hw : WallAdj A a q := (mem_wallDarts_pair A a q).mp h'
      exact ⟨q, ⟨WallAdj_mem_nbhdPts hw, hw⟩, by rw [hp]⟩
    · rintro ⟨w, ⟨hw1, hw2⟩, heq⟩
      have heq' : ((p, q) : (ℤ × ℤ) × (ℤ × ℤ)) = (a, w) := heq.symm
      exact ⟨by rw [heq']; exact (mem_wallDarts_pair A a w).mpr hw2,
        congrArg Prod.fst heq'⟩
  show ((wallDarts A).filter (fun e => e.1 = a)).card = WallDeg A a
  rw [himg, Finset.card_image_of_injective _ (fun w w' h => by simpa using congrArg Prod.snd h),
    WallDeg, Finset.card_filter]

theorem wallDarts_deg_even (A : Finset (ℤ × ℤ)) (a : ℤ × ℤ) :
    Even (DartGraph.deg (wallDartGraph A) a) := by
  rw [deg_eq_WallDeg]
  exact even_WallDeg A a

end Work.HornSC.CellBoundaryJordan
