import Mathlib
import Submission.Work.Horn.critval_or_contra
import Submission.Work.Horn.spreadChain_spec
import Submission.Work.Horn.germF0_base

namespace Work.Horn

open Set Filter Topology
open scoped Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- `pushdown E` vanishes exactly at `0`. -/
private theorem pushdown_eq_zero_iff' {E : ℂ → ℂ} {ζ : ℂ} :
    MandelDim.pushdown E ζ = 0 ↔ ζ = 0 := by
  by_cases h : ζ = 0
  · subst h; simp [MandelDim.pushdown]
  · rw [MandelDim.pushdown, if_neg h]
    exact ⟨fun hh => absurd hh (Work.Horn.MandelDim.piExp_ne_zero _), fun hh => absurd hh h⟩

/-- **The Liouville core of Shishikura's Lemma 5.2.**

`U` is a bounded open set, `G` maps `U` into itself and *onto* itself and is injective on `U`,
`P ⊆ U` is `G`-forward-invariant, `Φ` is an Abel coordinate on `U` (`Φ (G z) = Φ z + 1`),
injective on `P` and the tail of every horizontal strip is contained in `Φ '' P`, and every
`U`-orbit enters `P`.  Under these hypotheses `Φ` would be a bijection `U → ℂ` (injectivity on
`P` is transported to `U` because orbits enter `P`; surjectivity comes from the strips and the
fact that `G` is onto, which lets the Abel equation be run backwards), so its inverse is a
bounded entire function — constant, whence `1 = 0`. -/
private theorem false_of_abel_spread {G : ℂ → ℂ} {U P : Set ℂ} {Φ : ℂ → ℂ}
    (hUopen : IsOpen U) (hbdd : Bornology.IsBounded U) (hPsub : P ⊆ U)
    (hmap : Set.MapsTo G U U) (hsurj : U ⊆ G '' U) (hinj : Set.InjOn G U)
    (hPmap : G '' P ⊆ P)
    (hΦdiff : DifferentiableOn ℂ Φ U) (habel : ∀ z ∈ U, Φ (G z) = Φ z + 1)
    (hΦinj : Set.InjOn Φ P)
    (hstrip : ∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ P, Φ z = w)
    (henter : ∀ z ∈ U, ∃ n : ℕ, G^[n] z ∈ P) : False := by
  have hPmapM : Set.MapsTo G P P := fun x hx => hPmap ⟨x, hx, rfl⟩
  -- the Abel equation, iterated
  have hiter : ∀ (n : ℕ) (z : ℂ), z ∈ U → G^[n] z ∈ U ∧ Φ (G^[n] z) = Φ z + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro z hz; exact ⟨hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨hmem, hval⟩ := ih z hz
      rw [Function.iterate_succ_apply']
      exact ⟨hmap hmem, by rw [habel (G^[n] z) hmem, hval]; push_cast; ring⟩
  -- `Φ` is injective on all of `U`
  have hΦinjU : Set.InjOn Φ U := by
    intro u hu v hv huv
    obtain ⟨n₁, hn₁⟩ := henter u hu
    obtain ⟨n₂, hn₂⟩ := henter v hv
    have hNu : G^[max n₁ n₂] u ∈ P := by
      rw [← Nat.sub_add_cancel (le_max_left n₁ n₂), Function.iterate_add_apply]
      exact (hPmapM.iterate (max n₁ n₂ - n₁)) hn₁
    have hNv : G^[max n₁ n₂] v ∈ P := by
      rw [← Nat.sub_add_cancel (le_max_right n₁ n₂), Function.iterate_add_apply]
      exact (hPmapM.iterate (max n₁ n₂ - n₂)) hn₂
    have hvalU := (hiter (max n₁ n₂) u hu).2
    have hvalV := (hiter (max n₁ n₂) v hv).2
    have heq : Φ (G^[max n₁ n₂] u) = Φ (G^[max n₁ n₂] v) := by rw [hvalU, hvalV, huv]
    have hGu : G^[max n₁ n₂] u = G^[max n₁ n₂] v := hΦinj hNu hNv heq
    exact (hinj.iterate hmap (max n₁ n₂)) hu hv hGu
  -- `Φ` is onto `ℂ`
  have hΦsurj : Φ '' U = univ := by
    ext w
    simp only [mem_image, mem_univ, iff_true]
    have hstep : ∀ w : ℂ, w ∈ Φ '' U → w - 1 ∈ Φ '' U := by
      rintro w ⟨z, hzU, rfl⟩
      obtain ⟨z', hz'U, hz'⟩ := hsurj hzU
      exact ⟨z', hz'U, by rw [← hz', habel z' hz'U]; ring⟩
    have hsub : ∀ (n : ℕ) (w : ℂ), w ∈ Φ '' U → w - (n : ℂ) ∈ Φ '' U := by
      intro n
      induction n with
      | zero => intro w hw; simpa using hw
      | succ n ih =>
        intro w hw
        have : w - ((n + 1 : ℕ) : ℂ) = (w - 1) - (n : ℂ) := by push_cast; ring
        rw [this]
        exact ih (w - 1) (hstep w hw)
    obtain ⟨C, hC⟩ := hstrip (|w.im|)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, C < w.re + N := by
      obtain ⟨N, hN⟩ := exists_nat_gt (C - w.re)
      exact ⟨N, by linarith⟩
    obtain ⟨z, hzP, hz⟩ : ∃ z ∈ P, Φ z = w + (N : ℂ) :=
      hC (w + (N : ℂ)) (by simp [hN]) (by simp)
    have hw : w = (w + (N : ℂ)) - (N : ℂ) := by ring
    rw [hw, ← hz]
    exact hsub N (Φ z) ⟨z, hPsub hzP, rfl⟩
  -- the inverse of `Φ` is a bounded entire function
  have hψdiff : DifferentiableOn ℂ (Function.invFunOn Φ U) (Φ '' U) :=
    Work.Repel.invFunOn_differentiableOn hUopen hΦinjU hΦdiff
  have hψdiff' : Differentiable ℂ (Function.invFunOn Φ U) := by
    rw [← differentiableOn_univ, ← hΦsurj]
    exact hψdiff
  have hψmem : Set.range (Function.invFunOn Φ U) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ Φ '' U := by rw [hΦsurj]; exact mem_univ w
    exact Function.invFunOn_mem (by simpa using hw)
  have hbddψ : Bornology.IsBounded (Set.range (Function.invFunOn Φ U)) := hbdd.subset hψmem
  obtain ⟨c, hc⟩ := hψdiff'.exists_const_forall_eq_of_bounded hbddψ
  have hconst : ∀ w : ℂ, w = Φ c := by
    intro w
    have h1 : Φ (Function.invFunOn Φ U w) = w :=
      Function.invFunOn_eq (by
        have hw : w ∈ Φ '' U := by rw [hΦsurj]; exact mem_univ w
        simpa using hw)
    rw [hc w] at h1
    exact h1.symm
  have hbad : (Φ c + 1 : ℂ) = Φ c := hconst (Φ c + 1)
  have hone : (1 : ℂ) = 0 := by linear_combination hbad
  exact one_ne_zero hone

-- NOTE for the lead: the proof shows that the hypotheses after the `let` are in fact
-- INCONSISTENT: `W (n+1) i -> W n i` bijective for all `n` (hBij) plus the nesting of the
-- chain (which hBij forces, since `G '' W (n+1) i = W n i` together with the definitional
-- inclusion `G '' W (n+1) i ⊆ W n i` makes `G` injective on `⋃ n, W n i` and onto) make
-- `G : ⋃ n, W n i -> ⋃ n, W n i` a bijection; together with the Abel coordinate `Φ`, whose
-- injectivity on `V i` and strip-tail property propagate to all of `⋃ n, W n i` (orbits enter
-- `V i`, and the Abel equation can be run backwards because `G` is onto), this makes `Φ` a
-- bijection from the bounded `U` onto `ℂ` -- refuted by Liouville.  So the conclusion (and hence
-- the intended `v ∉ ⋃ n, W n i` contradiction of the caller) follows.  The hypothesis
-- `πExp (d.Φ c) ∉ ⋃ n, W n i` is NOT used.
theorem critPoint_of_component_of_ne_critval {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (hF0 : MandelDim.InF0 f₀ D₀) (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    (hB : MandelDim.IsImmediateBasin f₀ D₀ B) (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (c : ℂ) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    {q : ℕ} {V : Fin q → Set ℂ} (hVopen : ∀ (i : Fin q), IsOpen (V i))
    (hVsub : ∀ (i : Fin q), V i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
    (hVmap : ∀ (i : Fin q), ∀ z ∈ V i, MandelDim.pushdown d.E z ∈ V i ∪ {0})
    (hVne : ∀ (i : Fin q), (0 : ℂ) ∉ V i)
    (i : Fin q) :
    let W : ℕ → Fin q → Set ℂ := Work.Horn.spreadChain (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) V
    (∀ (n : ℕ), Set.BijOn (MandelDim.pushdown d.E) (W (n + 1) i) (W n i)) →
    SimplyConnectedSpace (⋃ n, W n i) →
    Bornology.IsBounded (⋃ n, W n i) →
    (∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (⋃ n, W n i) ∧
      (∀ z ∈ ⋃ n, W n i, Φ (MandelDim.pushdown d.E z) = Φ z + 1) ∧
      Set.InjOn Φ (V i) ∧
      (∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ V i, Φ z = w)) →
    (∀ z ∈ ⋃ n, W n i, ∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ V i) →
    MandelDim.piExp (d.Φ c) ∉ ⋃ n, W n i →
    ∃ z ∈ ⋃ n, W n i, deriv (MandelDim.pushdown d.E) z = 0 := by
  intro W hBij hBsc hbdd hPhi henter hnotmem
  obtain ⟨Φ, hΦdiff, habel, hΦinjV, hstrip⟩ := hPhi
  -- abbreviations
  set G : ℂ → ℂ := MandelDim.pushdown d.E with hGdef
  set Dc : Set ℂ := insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) with hDcdef
  set U : Set ℂ := ⋃ n, W n i with hUdef
  -- the horn domain is open and `G` is holomorphic there, and `G` vanishes only at `0`
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDopen : IsOpen Dc := by rw [hDcdef]; exact isOpen_insert_piExp hBuO hBlO hup hlo
  have hGholo : DifferentiableOn ℂ G Dc := by
    rw [hGdef, hDcdef]
    exact pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have hGzero : ∀ {z : ℂ}, G z = 0 → z = 0 := by
    intro z hz
    rw [hGdef] at hz
    exact pushdown_eq_zero_iff'.mp hz
  -- the levels of the spread chain, against the definition of `spreadChain`
  have hWsucc : ∀ n : ℕ, W (n + 1) i = Work.Horn.spreadStep G Dc (W n) i := fun n => rfl
  have hWstep : ∀ n : ℕ, Work.Horn.spreadStep G Dc (W n) i =
      ⋃ x ∈ W n i, connectedComponentIn (Dc ∩ G ⁻¹' (W n i)) x := fun n => rfl
  have hW0 : W 0 i = V i := rfl
  -- each level is open and sits inside `Dc`
  have hWsubD : ∀ n : ℕ, W n i ⊆ Dc := by
    intro n
    induction n with
    | zero => rw [hW0]; exact hVsub i
    | succ n ih =>
      rw [hWsucc n, hWstep n]
      intro z hz
      obtain ⟨x, -, hzcc⟩ := Set.mem_iUnion₂.mp hz
      exact (connectedComponentIn_subset _ _ hzcc).1
  have hWopen : ∀ n : ℕ, IsOpen (W n i) := by
    intro n
    induction n with
    | zero => rw [hW0]; exact hVopen i
    | succ n ih =>
      rw [hWsucc n, hWstep n]
      refine isOpen_iUnion fun x => isOpen_iUnion fun _ => ?_
      have hUo : IsOpen (Dc ∩ G ⁻¹' (W n i)) :=
        hGholo.continuousOn.isOpen_inter_preimage hDopen ih
      exact hUo.connectedComponentIn
  -- the petal is forward invariant
  have hGWV : G '' V i ⊆ V i := by
    rintro y ⟨z, hz, rfl⟩
    rcases hVmap i z hz with h | h
    · exact h
    · have h0V : (0 : ℂ) ∈ V i := hGzero h ▸ hz
      exact absurd h0V (hVne i)
  -- the next level is contained in the preimage of the current one (definitional)
  have hsci : ∀ n : ℕ, G '' W (n + 1) i ⊆ W n i := by
    intro n
    rintro y ⟨z, hz, rfl⟩
    rw [hWsucc n, hWstep n] at hz
    obtain ⟨x, -, hzcc⟩ := Set.mem_iUnion₂.mp hz
    exact (connectedComponentIn_subset _ _ hzcc).2
  -- nesting and forward invariance of each level
  have hkey : ∀ n : ℕ, (G '' W n i ⊆ W n i) ∧ (W n i ⊆ W (n + 1) i) := by
    intro n
    induction n with
    | zero =>
      have h0 : G '' W 0 i ⊆ W 0 i := by rw [hW0]; exact hGWV
      refine ⟨h0, ?_⟩
      rw [hW0, hWsucc 0, hWstep 0]
      intro z hz
      have hzV : z ∈ V i := hz
      exact Set.mem_iUnion₂.mpr ⟨z, hz, mem_connectedComponentIn ⟨hVsub i hzV, hGWV ⟨z, hzV, rfl⟩⟩⟩
    | succ n ih =>
      obtain ⟨hGWn, hnestn⟩ := ih
      have hGWs : G '' W (n + 1) i ⊆ W (n + 1) i := fun y hy => hnestn (hsci n hy)
      refine ⟨hGWs, ?_⟩
      rw [hWsucc (n + 1), hWstep (n + 1)]
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨z, hz,
        mem_connectedComponentIn ⟨hWsubD (n + 1) hz, hGWs ⟨z, hz, rfl⟩⟩⟩
  have hGW : ∀ n : ℕ, G '' W n i ⊆ W n i := fun n => (hkey n).1
  have hnest : ∀ n : ℕ, W n i ⊆ W (n + 1) i := fun n => (hkey n).2
  have hmono : Monotone (fun n : ℕ => W n i) := monotone_nat_of_le_succ hnest
  -- `G` maps level `n + 1` bijectively onto level `n`
  have honto : ∀ n : ℕ, G '' W (n + 1) i = W n i := by
    intro n
    refine le_antisymm (hsci n) ?_
    intro z hz
    obtain ⟨y, hy, hyz⟩ := (hBij n).2.2 hz
    exact ⟨y, hy, hyz⟩
  have hinjL : ∀ n : ℕ, Set.InjOn G (W (n + 1) i) := fun n => (hBij n).2.1
  -- facts about the union `U`
  have hUmem : ∀ z : ℂ, z ∈ U ↔ ∃ n : ℕ, z ∈ W n i := by
    intro z; rw [hUdef]; exact Set.mem_iUnion
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_iUnion fun n => hWopen n
  have hUsubD : U ⊆ Dc := by
    intro z hz
    obtain ⟨n, hn⟩ := (hUmem z).mp hz
    exact hWsubD n hn
  have hGdiffU : DifferentiableOn ℂ G U := hGholo.mono hUsubD
  have hmapU : Set.MapsTo G U U := by
    intro z hz
    obtain ⟨n, hn⟩ := (hUmem z).mp hz
    exact (hUmem (G z)).mpr ⟨n, hGW n ⟨z, hn, rfl⟩⟩
  have hsurjU : U ⊆ G '' U := by
    intro z hz
    obtain ⟨n, hn⟩ := (hUmem z).mp hz
    have hz' : z ∈ G '' W (n + 1) i := by rw [honto n]; exact hn
    obtain ⟨y, hy, hyz⟩ := hz'
    exact ⟨y, (hUmem y).mpr ⟨n + 1, hy⟩, hyz⟩
  have hGinjU : Set.InjOn G U := by
    intro u hu v hv huv
    obtain ⟨n, hn⟩ := (hUmem u).mp hu
    obtain ⟨m, hm⟩ := (hUmem v).mp hv
    set k : ℕ := max n m + 1 with hkdef
    have hkpos : 0 < k := Nat.succ_pos _
    have huk : u ∈ W k i := hmono (by omega) hn
    have hvk : v ∈ W k i := hmono (by omega) hm
    have hpred : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hkpos
    have hinj := hinjL (k - 1)
    rw [hpred] at hinj
    exact hinj huk hvk huv
  -- finally, the Liouville argument with `P = V i`
  exact (false_of_abel_spread (G := G) (U := U) (P := V i) (Φ := Φ) hUopen hbdd
    (by rw [← hW0]; intro z hz; exact (hUmem z).mpr ⟨0, hz⟩)
    hmapU hsurjU hGinjU hGWV hΦdiff habel hΦinjV hstrip henter).elim

end Work.Horn
