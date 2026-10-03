import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UnitInterval

namespace Commons.Topology.Homotopy

open Set
open scoped Topology

/-- **Gluing for a "chamber" decomposition.**  Let `U` be a topological space, `S ⊆ U` a
"spine" and `c : ℕ → Set U` a sequence of pairwise disjoint "chambers" disjoint from `S`, whose
closures cover `U` locally (their boundaries lie in `S`), together with folds `Φ n` each supported
on `c n`, fixing `S`, staying in `c n ∪ S` and ending in `S`.  Then `U` strongly deformation
retracts onto `S`. -/
theorem deformationRetract_of_chamber_folds
    {U : Type*} [TopologicalSpace U] (c : ℕ → Set U) (S : Set U)
    (hcdisj : ∀ m n, m ≠ n → Disjoint (c m) (c n))
    (hcS : ∀ n, Disjoint (c n) S)
    (hbd : ∀ n ⦃x : U⦄, x ∈ closure (c n) → x ∉ c n → x ∈ S)
    (hint : ∀ x : U, ∃ n, x ∈ interior ((⋃ i ∈ Finset.range n, closure (c i)) ∪ S))
    (Φ : ℕ → U × unitInterval → U)
    (hΦcont : ∀ n, Continuous (Φ n)) (hΦ0 : ∀ n x, Φ n (x, 0) = x)
    (hΦid : ∀ n x, x ∈ S → ∀ t, Φ n (x, t) = x)
    (hΦout : ∀ n x, x ∉ c n → ∀ t, Φ n (x, t) = x)
    (hΦstay : ∀ n x, x ∈ c n → ∀ t, Φ n (x, t) ∈ c n ∪ S)
    (hΦ1 : ∀ n x, x ∈ c n → Φ n (x, 1) ∈ S) :
    ∃ H : U × unitInterval → U, Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) ∈ S) ∧ (∀ x, x ∈ S → ∀ t, H (x, t) = x) := by
  classical
  -- `G m` is the composition of the folds `Φ 0, …, Φ (m-1)` carried out "at the same time".
  let G : ℕ → U × unitInterval → U :=
    fun m => Nat.rec (fun p : U × unitInterval => p.1)
      (fun m rec => fun p => Φ m (rec p, p.2)) m
  have G_zero : ∀ p : U × unitInterval, G 0 p = p.1 := fun p => rfl
  have G_succ : ∀ (m : ℕ) (p : U × unitInterval), G (m + 1) p = Φ m (G m p, p.2) :=
    fun m p => rfl
  -- `G m` is continuous.
  have G_cont : ∀ m, Continuous (G m) := by
    intro m
    induction m with
    | zero =>
        rw [show G 0 = fun p : U × unitInterval => p.1 from funext G_zero]
        exact continuous_fst
    | succ m ih =>
        rw [show G (m + 1) = fun p : U × unitInterval => Φ m (G m p, p.2) from funext (G_succ m)]
        exact (hΦcont m).comp (ih.prodMk continuous_snd)
  -- Structural facts about the composition.
  have G_nmem : ∀ (m : ℕ) (x : U) (t : unitInterval),
      (∀ j, j < m → x ∉ c j) → G m (x, t) = x := by
    intro m
    induction m with
    | zero => intro x t _; exact G_zero (x, t)
    | succ m ih =>
        intro x t hx
        rw [G_succ m (x, t)]
        have hxm : x ∉ c m := hx m (Nat.lt_succ_self m)
        have hGm : G m (x, t) = x :=
          ih x t (fun j hj => hx j (Nat.lt_trans hj (Nat.lt_succ_self m)))
        rw [hGm, hΦout m x hxm t]
  have G_mem : ∀ (m j : ℕ) (x : U) (t : unitInterval),
      j < m → x ∈ c j → G m (x, t) = Φ j (x, t) := by
    intro m
    induction m with
    | zero => intro j x t hj _; exact absurd hj (Nat.not_lt_zero j)
    | succ m ih =>
        intro j x t hj hxj
        rw [G_succ m (x, t)]
        by_cases hjm : j < m
        · have hGm : G m (x, t) = Φ j (x, t) := ih j x t hjm hxj
          have hyS : Φ j (x, t) ∈ c j ∪ S := hΦstay j x hxj t
          have hym : Φ j (x, t) ∉ c m := by
            rcases hyS with h | h
            · exact fun hcm => (Set.disjoint_left.mp (hcdisj j m (ne_of_lt hjm)) h) hcm
            · exact fun hcm => (Set.disjoint_left.mp (hcS m) hcm) h
          rw [hGm, hΦout m (Φ j (x, t)) hym t]
        · have hjm' : j = m := by omega
          rw [hjm'] at hxj ⊢
          have hGm : G m (x, t) = x :=
            G_nmem m x t (fun i hi => by
              exact fun hci => (Set.disjoint_left.mp (hcdisj i m (by omega)) hci) hxj)
          rw [hGm]
  -- Every point lies in `S` or in exactly one chamber.
  have cover : ∀ x : U, x ∈ S ∨ ∃ i, x ∈ c i := by
    intro x
    obtain ⟨n, hn⟩ := hint x
    have hxA : x ∈ (⋃ i ∈ Finset.range n, closure (c i)) ∪ S := interior_subset hn
    rcases hxA with hA | hS
    · obtain ⟨i, _hi, hxi⟩ := mem_iUnion₂.mp hA
      by_cases hci : x ∈ c i
      · exact Or.inr ⟨i, hci⟩
      · exact Or.inl (hbd i hxi hci)
    · exact Or.inl hS
  -- Choose for each point a neighbourhood meeting only finitely many chambers.
  let N : U → ℕ := fun x => Classical.choose (hint x)
  have hN : ∀ x, x ∈ interior ((⋃ i ∈ Finset.range (N x), closure (c i)) ∪ S) :=
    fun x => Classical.choose_spec (hint x)
  let W : U → Set U := fun x => interior ((⋃ i ∈ Finset.range (N x), closure (c i)) ∪ S)
  have hxW : ∀ x, x ∈ W x := fun x => hN x
  have W_nmem : ∀ x y, y ∈ W x → ∀ i, N x ≤ i → y ∉ c i := by
    intro x y hy i hi hyi
    have hyA : y ∈ (⋃ i ∈ Finset.range (N x), closure (c i)) ∪ S := interior_subset hy
    rcases hyA with hA | hyS
    · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hA
      have hji : j ≠ i := by
        intro h; rw [h] at hj; exact (not_lt.mpr hi) (Finset.mem_range.mp hj)
      have hyj' : y ∉ c j := fun hcj => (Set.disjoint_left.mp (hcdisj j i hji) hcj) hyi
      exact (Set.disjoint_left.mp (hcS i) hyi) (hbd j hyj hyj')
    · exact (Set.disjoint_left.mp (hcS i) hyi) hyS
  -- The defining formula stabilises: it only depends on the finitely many folds that matter.
  have key : ∀ (x : U) (p : U × unitInterval), p.1 ∈ W x → G (N p.1) p = G (N x) p := by
    intro x p hp
    rcases p with ⟨y, t⟩
    by_cases hex : ∃ j, y ∈ c j
    · obtain ⟨j, hyj⟩ := hex
      have hjx : j < N x := by
        by_contra h; exact W_nmem x y hp j (not_lt.mp h) hyj
      have hjy : j < N y := by
        by_contra h; exact W_nmem y y (hxW y) j (not_lt.mp h) hyj
      rw [G_mem (N y) j y t hjy hyj, G_mem (N x) j y t hjx hyj]
    · push Not at hex
      rw [G_nmem (N y) y t (fun j _ => hex j), G_nmem (N x) y t (fun j _ => hex j)]
  have Hcont : Continuous (fun p : U × unitInterval => G (N p.1) p) := by
    apply continuous_of_cover_nhds (s := fun x : U => W x ×ˢ (Set.univ : Set unitInterval))
    · intro p
      exact ⟨p.1, (isOpen_interior.prod isOpen_univ).mem_nhds ⟨hxW p.1, Set.mem_univ _⟩⟩
    · intro x
      exact ContinuousOn.congr ((G_cont (N x)).continuousOn)
        (fun p hp => key x p hp.1)
  refine ⟨fun p => G (N p.1) p, Hcont, ?_, ?_, ?_⟩
  · intro x
    show G (N x) (x, 0) = x
    rcases cover x with hxS | ⟨j, hxj⟩
    · exact G_nmem (N x) x 0 (fun i _ => fun hci => (Set.disjoint_left.mp (hcS i) hci) hxS)
    · have hjx : j < N x := by
        by_contra h; exact W_nmem x x (hxW x) j (not_lt.mp h) hxj
      rw [G_mem (N x) j x 0 hjx hxj, hΦ0 j x]
  · intro x
    show G (N x) (x, 1) ∈ S
    rcases cover x with hxS | ⟨j, hxj⟩
    · have : G (N x) (x, 1) = x :=
        G_nmem (N x) x 1 (fun i _ => fun hci => (Set.disjoint_left.mp (hcS i) hci) hxS)
      rw [this]; exact hxS
    · have hjx : j < N x := by
        by_contra h; exact W_nmem x x (hxW x) j (not_lt.mp h) hxj
      rw [G_mem (N x) j x 1 hjx hxj]; exact hΦ1 j x hxj
  · intro x hxS t
    show G (N x) (x, t) = x
    exact G_nmem (N x) x t (fun i _ => fun hci => (Set.disjoint_left.mp (hcS i) hci) hxS)

end Commons.Topology.Homotopy