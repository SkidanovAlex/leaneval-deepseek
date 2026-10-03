import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Every fibre of the (unperturbed) Fatou coordinate `Φ` is infinite

`Work.Horn.Phi_fiber_infinite` — used by the HORN area to get the infinite degree of the
horn map (Shishikura, Prop. 5.3).

Mathematical content (elementary, no analysis beyond `Φ ∘ f₀ = Φ + 1`):
let `B` be an immediate parabolic basin, `Φ` the Fatou coordinate on the basin, so that
`Φ (f₀ z) = Φ z + 1` on `B`, and suppose that
* `f₀ : B → B` is at least two-to-one over every point of `B` except (possibly) the single
  point `f₀ c` (`htwo`), and
* `Φ` is onto `ℂ` (`honto`).

Write `S n = {z ∈ B | Φ z = y + n}` for a fixed `y`.  Then `f₀ '' S n = S (n+1)`, all `S n`
are nonempty, and every point of `S (n+1)` other than `f₀ c` has at least two preimages in
`S n`.  Hence `f₀ : S n → S (n+1)` is surjective, and it is not injective as soon as
`S (n+1) ≠ {f₀ c}`; so `n ↦ |S n|` is non-increasing in `ℕ` and strictly decreasing at each
step at which `S (n+1) ≠ {f₀ c}`.  Assuming `S 0` finite, this forces `|S N| = 1` for
`N = |S 0|`, and then an induction on `n` shows `S n = {f₀ c}` for every `n ≥ N`, which is
absurd since `Φ (f₀ c) = y + N + 1` and `= y + N + 2`.
-/

namespace Work.Horn

set_option linter.style.haveILetI false

open Set

theorem Phi_fiber_infinite {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀)
    (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hcB : c ∈ B)
    (htwo : ∀ a ∈ B, a ≠ f₀ c → ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ f₀ x = a ∧ f₀ y = a)
    (honto : ∀ y : ℂ, ∃ z ∈ B, d.Φ z = y) :
    ∀ y : ℂ, {z : ℂ | z ∈ B ∧ d.Φ z = y}.Infinite := by
  obtain ⟨-, -, hBbasin, -, hBmap, hBsurj, -⟩ := hB
  -- the Abel equation on the basin
  have habel : ∀ z ∈ B, d.Φ (f₀ z) = d.Φ z + 1 := fun z hz => d.Φ_abel z (hBbasin hz)
  intro y hf
  -- candidate infinite fibre, level by level
  set S : ℕ → Set ℂ := fun n => {z : ℂ | z ∈ B ∧ d.Φ z = y + n} with hSdef
  have hS : ∀ n, S n = {z : ℂ | z ∈ B ∧ d.Φ z = y + n} := fun n => congrFun hSdef n
  have hSmem : ∀ n z, z ∈ S n ↔ z ∈ B ∧ d.Φ z = y + n := by
    intro n z
    rw [hS n]
    exact Iff.rfl
  have hS0 : S 0 = {z : ℂ | z ∈ B ∧ d.Φ z = y} := by
    rw [hS 0]
    congr 1
    ext z
    simp
  have hf0 : (S 0).Finite := hS0 ▸ hf
  -- `↑(n+1) = ↑n + 1` for the target levels
  have hcast : ∀ n : ℕ, y + ((n + 1 : ℕ) : ℂ) = y + (n : ℂ) + 1 := by
    intro n; push_cast; ring
  -- `f₀ '' S n = S (n+1)`: forward inclusion from the Abel equation, backward from
  -- `B ⊆ f₀ '' B`
  have himage : ∀ n, f₀ '' S n = S (n + 1) := by
    intro n
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hzB, hzΦ⟩ := (hSmem n z).mp hz
      refine (hSmem (n + 1) (f₀ z)).mpr ⟨hBmap hzB, ?_⟩
      rw [habel z hzB, hzΦ, hcast n]
    · intro a ha
      obtain ⟨haB, haΦ⟩ := (hSmem (n + 1) a).mp ha
      rw [hcast n] at haΦ
      obtain ⟨w, hwB, hw⟩ := hBsurj haB
      refine ⟨w, ?_, hw⟩
      refine (hSmem n w).mpr ⟨hwB, ?_⟩
      have h1 : d.Φ (f₀ w) = d.Φ w + 1 := habel w hwB
      rw [hw] at h1
      exact add_right_cancel (by rw [← h1, haΦ])
  have hfin : ∀ n, (S n).Finite := by
    intro n
    induction n with
    | zero => exact hf0
    | succ n ih => rw [← himage n]; exact ih.image f₀
  haveI : ∀ n, Fintype (S n) := fun n => (hfin n).fintype
  have hncard : ∀ n, (S n).ncard = Fintype.card (S n) := fun n => by
    rw [Set.ncard_eq_toFinset_card (S n) (hfin n), (hfin n).card_toFinset]
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    obtain ⟨z, hzB, hzΦ⟩ := honto (y + n)
    exact ⟨z, (hSmem n z).mpr ⟨hzB, hzΦ⟩⟩
  have hpos : ∀ n, 1 ≤ Fintype.card (S n) := by
    intro n
    obtain ⟨z, hz⟩ := hnonempty n
    have hp : 0 < Fintype.card (S n) := Fintype.card_pos_iff.mpr ⟨⟨z, hz⟩⟩
    omega
  -- the map induced by `f₀` on the levels
  have hsmaps : ∀ n, ∀ z : S n, f₀ z.1 ∈ S (n + 1) := by
    intro n z
    obtain ⟨hzB, hzΦ⟩ := (hSmem n z.1).mp z.2
    refine (hSmem (n + 1) (f₀ z.1)).mpr ⟨hBmap hzB, ?_⟩
    rw [habel z.1 hzB, hzΦ, hcast n]
  let F : ∀ n, S n → S (n + 1) := fun n z => ⟨f₀ z.1, hsmaps n z⟩
  have hFsurj : ∀ n, Function.Surjective (F n) := by
    intro n b
    have hb : b.1 ∈ f₀ '' S n := by rw [himage n]; exact b.2
    obtain ⟨z, hz, hzf⟩ := hb
    exact ⟨⟨z, hz⟩, Subtype.ext hzf⟩
  -- where a preimage of a point of `S (n+1)` lives
  have hfib : ∀ n a, a ∈ S (n + 1) → ∀ z ∈ B, f₀ z = a → d.Φ z = y + n := by
    intro n a ha z hzB hfz
    have haΦ := ((hSmem (n + 1) a).mp ha).2
    rw [hcast n] at haΦ
    have h1 : d.Φ (f₀ z) = d.Φ z + 1 := habel z hzB
    have h2 : d.Φ z + 1 = y + ↑n + 1 := by rw [← h1, hfz, haΦ]
    exact add_right_cancel h2
  -- strict decrease of the cardinalities
  have hstrict : ∀ n, S (n + 1) ≠ {f₀ c} →
      Fintype.card (S (n + 1)) < Fintype.card (S n) := by
    intro n hne
    apply Fintype.card_lt_of_surjective_not_injective (F n) (hFsurj n)
    intro hinj
    have hex : ∃ a ∈ S (n + 1), a ≠ f₀ c := by
      by_contra h
      have h' : ∀ a, a ∈ S (n + 1) → a = f₀ c := by
        intro a ha
        by_contra hne'
        exact h ⟨a, ha, hne'⟩
      obtain ⟨z, hz⟩ := hnonempty (n + 1)
      exact hne (Set.eq_singleton_iff_unique_mem.mpr
        ⟨by rw [← h' z hz]; exact hz, fun b hb => h' b hb⟩)
    obtain ⟨a, haS, ha⟩ := hex
    have haB : a ∈ B := ((hSmem (n + 1) a).mp haS).1
    obtain ⟨u, huB, w, hwB, huw, hfu, hfw⟩ := htwo a haB ha
    have huS : u ∈ S n := (hSmem n u).mpr ⟨huB, hfib n a haS u huB hfu⟩
    have hwS : w ∈ S n := (hSmem n w).mpr ⟨hwB, hfib n a haS w hwB hfw⟩
    have heq : F n ⟨u, huS⟩ = F n ⟨w, hwS⟩ :=
      Subtype.ext (by show f₀ u = f₀ w; rw [hfu, hfw])
    exact huw (Subtype.ext_iff.mp (hinj heq))
  -- the cardinalities reach `1`
  have hexN : ∃ N, Fintype.card (S N) = 1 := by
    by_contra h
    have h2 : ∀ n, 2 ≤ Fintype.card (S n) := by
      intro n
      have h1 := hpos n
      have hne1 : Fintype.card (S n) ≠ 1 := fun heq => h ⟨n, heq⟩
      omega
    have hbound : ∀ n, Fintype.card (S n) + n ≤ Fintype.card (S 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hne : S (k + 1) ≠ {f₀ c} := by
          intro hc
          have hle : Fintype.card (S (k + 1)) ≤ 1 := by
            rw [Fintype.card_le_one_iff]
            intro a b
            apply Subtype.ext
            have ha : a.1 = f₀ c := Set.mem_singleton_iff.mp (hc ▸ a.2)
            have hb : b.1 = f₀ c := Set.mem_singleton_iff.mp (hc ▸ b.2)
            rw [ha, hb]
          have h2' := h2 (k + 1)
          omega
        have hs := hstrict k hne
        omega
    have hcontra := hbound (Fintype.card (S 0) + 1)
    have hp1 := hpos (Fintype.card (S 0) + 1)
    omega
  obtain ⟨N, hN⟩ := hexN
  -- a singleton level must consist of a preimage of the critical value `f₀ c`
  have hkey : ∀ n p, S n = {p} → f₀ p = f₀ c := by
    intro n p hp
    by_contra hpc
    have hpS : p ∈ S n := by rw [hp]; exact Set.mem_singleton_iff.mpr rfl
    obtain ⟨hpB, hpΦ⟩ := (hSmem n p).mp hpS
    obtain ⟨u, huB, w, hwB, huw, hfu, hfw⟩ := htwo (f₀ p) (hBmap hpB) hpc
    have huS : u ∈ S n := (hSmem n u).mpr ⟨huB, by
      have h1 : d.Φ (f₀ u) = d.Φ u + 1 := habel u huB
      have h2 : d.Φ (f₀ u) = y + ↑n + 1 := by rw [hfu, habel p hpB, hpΦ]
      rw [h1] at h2
      exact add_right_cancel h2⟩
    have hwS : w ∈ S n := (hSmem n w).mpr ⟨hwB, by
      have h1 : d.Φ (f₀ w) = d.Φ w + 1 := habel w hwB
      have h2 : d.Φ (f₀ w) = y + ↑n + 1 := by rw [hfw, habel p hpB, hpΦ]
      rw [h1] at h2
      exact add_right_cancel h2⟩
    have hup : u = p := by rw [hp] at huS; exact Set.mem_singleton_iff.mp huS
    have hwp : w = p := by rw [hp] at hwS; exact Set.mem_singleton_iff.mp hwS
    exact huw (hup.trans hwp.symm)
  obtain ⟨p, hp⟩ := Fintype.card_eq_one_iff.mp hN
  have hSN : S N = {p.1} := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff]
      exact congrArg Subtype.val (hp ⟨z, hz⟩)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact p.2
  have hS1 : S (N + 1) = {f₀ c} := by
    rw [← himage N, hSN, Set.image_singleton, hkey N p.1 hSN]
  -- `S (N+1)` is a singleton too, so it must consist of a preimage of `f₀ c`,
  -- i.e. `f₀ (f₀ c) = f₀ c`; but then `Φ (f₀ (f₀ c)) = Φ (f₀ c) + 1`.
  have hff : f₀ (f₀ c) = f₀ c := hkey (N + 1) (f₀ c) hS1
  have h1 : d.Φ (f₀ (f₀ c)) = d.Φ (f₀ c) + 1 := habel (f₀ c) (hBmap hcB)
  rw [hff] at h1
  have h01 : (0 : ℂ) = 1 := add_left_cancel (by rw [add_zero]; exact h1)
  exact zero_ne_one h01

end Work.Horn
