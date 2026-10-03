import Mathlib
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.mem_winRho_range_iff
import Submission.Work.OROneRel.presentedGroup_union_amalgam
import Submission.Work.OROneRel.unionAmalgam_normalForm
import Submission.Work.OROneRel.gateBookkeeping
import Submission.Work.OROneRel.bandLoopsDefs
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.band_lpow_levels
import Submission.Work.OROneRel.invRev_levels
import Submission.Work.OROneRel.invRev_lpow_levels

/-!
# The intersection formula for the two halves of the band vertex

This file proves `Work.OROneRel.band_halves_inter`, the intersection formula

  `tlPle c ⊓ tlPge (c+1) = tlAk c`

for the two halves of the line of translated band vertices of the two-letter band.

The proof rests on the observation that the "subgroup of loops of the `ℤ`-cover with prescribed
edge set" is *canonically* described by the reduced word: `x ∈ loopsInE c E` iff the reduced word
`wordOf x` (which is the free reduction of *any* word representing `x`) has all its decorated edges
in `E`.  Free reduction only deletes levels of the walk (`band_reduce`, `decor_sublist_of_red`), so
the level window conditions become conditions on the *canonical* reduced word; consequently the two
halves intersect exactly in the gate by pure logic on the level bounds.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

section Band

variable (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
variable (Wt : ℤ → FreeGroup (Fin 2))

/-- **The membership dictionary of the translated band vertices**: `x ∈ tlHk k` iff its
`τ^{-k}`-conjugate lies in the band vertex `tlH`. -/
theorem mem_tlHk_iff_local (k : ℤ) (x : FreeGroup (Fin 2)) :
    x ∈ tlHk p q hp hq hcop Wt k ↔
      (tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k ∈ tlH p q Wt := by
  rw [tlHk, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (tlLowTau p q hp hq hcop) ^ k * y *
        ((tlLowTau p q hp hq hcop) ^ k)⁻¹ = x := hyx
    have hA : (tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k = y := by
      rw [← hyx', ← zpow_neg (tlLowTau p q hp hq hcop) k]
      group
    rw [hA]
    exact hy
  · intro hx
    refine ⟨(tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k, hx, ?_⟩
    show (tlLowTau p q hp hq hcop) ^ k *
        ((tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k) *
        ((tlLowTau p q hp hq hcop) ^ k)⁻¹ = x
    rw [← zpow_neg (tlLowTau p q hp hq hcop) k]
    group

/-- Conjugating a translated band vertex by a power of the deck element shifts it. -/
theorem mem_tlHk_conj (k a : ℤ) {y : FreeGroup (Fin 2)}
    (hy : y ∈ tlHk p q hp hq hcop Wt k) :
    (MulAut.conj ((tlLowTau p q hp hq hcop) ^ a)) y ∈ tlHk p q hp hq hcop Wt (k + a) := by
  rw [mem_tlHk_iff_local] at hy ⊢
  have key : (tlLowTau p q hp hq hcop) ^ (-(k + a)) *
        ((MulAut.conj ((tlLowTau p q hp hq hcop) ^ a)) y) *
        (tlLowTau p q hp hq hcop) ^ (k + a)
      = (tlLowTau p q hp hq hcop) ^ (-k) * y * (tlLowTau p q hp hq hcop) ^ k := by
    rw [MulAut.conj_apply]
    conv_rhs =>
      rw [show (tlLowTau p q hp hq hcop) ^ (-k) =
          (tlLowTau p q hp hq hcop) ^ (-(k + a)) * (tlLowTau p q hp hq hcop) ^ a from by
        rw [← zpow_add]; congr 1; ring]
    conv_rhs =>
      rw [show (tlLowTau p q hp hq hcop) ^ k =
          ((tlLowTau p q hp hq hcop) ^ a)⁻¹ * (tlLowTau p q hp hq hcop) ^ (k + a) from by
        rw [← zpow_neg (tlLowTau p q hp hq hcop) a, ← zpow_add]; congr 1; ring]
    group
  rw [key]
  exact hy

/-- **Transporting the lower half**: conjugating by `τ^a` shifts `tlPle` by `a`. -/
theorem tlPle_conj_le (c a : ℤ) :
    tlPle p q hp hq hcop Wt c ≤
      (tlPle p q hp hq hcop Wt (c + a)).comap
        (MulAut.conj ((tlLowTau p q hp hq hcop) ^ a)).toMonoidHom := by
  rw [tlPle]
  refine (Subgroup.closure_le (K := _)).mpr ?_
  rintro y ⟨k, hk, hyk⟩
  exact Subgroup.subset_closure ⟨k + a, by omega, mem_tlHk_conj p q hp hq hcop Wt k a hyk⟩

/-- **Transporting the upper half**: conjugating by `τ^a` shifts `tlPge` by `a`. -/
theorem tlPge_conj_le (c a : ℤ) :
    tlPge p q hp hq hcop Wt c ≤
      (tlPge p q hp hq hcop Wt (c + a)).comap
        (MulAut.conj ((tlLowTau p q hp hq hcop) ^ a)).toMonoidHom := by
  rw [tlPge]
  refine (Subgroup.closure_le (K := _)).mpr ?_
  rintro y ⟨k, hk, hyk⟩
  exact Subgroup.subset_closure ⟨k + a, by omega, mem_tlHk_conj p q hp hq hcop Wt k a hyk⟩

/-- **The two edge sets of the halves intersect in the gate.** -/
theorem belowE_inter_aboveE {α : Type u} (c : α → ℤ) (M' M : ℤ) :
    belowE c M ∩ aboveE c M' = winE c M' M := by
  ext e
  rw [Set.mem_inter_iff, mem_belowE, mem_aboveE, mem_winE]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h3, h1, h4, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h2, h4⟩, h1, h3⟩

/-- **The band vertex is the loop subgroup of the window.** -/
theorem tlH_eq_loopsInE (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    tlH p q Wt = loopsInE (tlW p q) (winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨L, hwalk, hlsig, hmk⟩ :=
      (mem_winRho_range_iff p q hp hq hcop Wt hW0 hcoh hwin htree x).mp hx
    rw [mem_loopsInE_iff]
    exact ⟨L, hmk, hlsig, hwalk⟩
  · intro x hx
    obtain ⟨L, hmk, hlsig, hwalk⟩ := (mem_loopsInE_iff _ _ x).mp hx
    exact (mem_winRho_range_iff p q hp hq hcop Wt hW0 hcoh hwin htree x).mpr
      ⟨L, hwalk, hlsig, hmk⟩

/-- **The walk of the deck element lies in the band `[0,m]`.** -/
theorem tlTau_band :
    band (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (wordOf (tlLowTau p q hp hq hcop)) :=
  band_of_decor_winE (tlLowTau_walk p q hp hq hcop) le_rfl
    (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q))

/-- **The weight of the deck element is `1`.** -/
theorem tlTau_lsig :
    lsig (tlW p q) (wordOf (tlLowTau p q hp hq hcop)) = 1 := by
  rw [CoedgeBase.lsig_wordOf, tlLowTau_cohom p q hp hq hcop]
  rfl

/-- **The lower half `tlPle 0` is generated by loops of the half-plane `(-∞,m]`.** -/
theorem tlPle_zero_le_belowE (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    tlPle p q hp hq hcop Wt 0 ≤
      loopsInE (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ))) := by
  have hm : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) :=
    mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)
  have hTband := tlTau_band p q hp hq hcop
  have hTlsig := tlTau_lsig p q hp hq hcop
  have hH := tlH_eq_loopsInE (p := p) (q := q) (Wt := Wt) hp hq hcop hW0 hcoh hwin htree
  rw [tlPle]
  refine (Subgroup.closure_le (K := loopsInE (tlW p q) (belowE (tlW p q)
    ((p : ℤ) * (q : ℤ))))).mpr ?_
  rintro y ⟨k, hk, hyk⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -k :=
    ⟨(-k).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hkn : k = -(n : ℤ) := by omega
  set h := (tlLowTau p q hp hq hcop) ^ (-k) * y * (tlLowTau p q hp hq hcop) ^ k with hh
  have hhH : h ∈ tlH p q Wt := (mem_tlHk_iff_local p q hp hq hcop Wt k y).mp hyk
  have hy_eq : y = (tlLowTau p q hp hq hcop) ^ k * h *
      ((tlLowTau p q hp hq hcop) ^ k)⁻¹ := by
    rw [hh]; group
  have hh_mem : h ∈ loopsInE (tlW p q) (winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) := by
    rw [← hH]; exact hhH
  have hh_lsig : lsig (tlW p q) (wordOf h) = 0 := by
    rw [CoedgeBase.lsig_wordOf, hh_mem.1]
    simp
  have hh_levLe : levLe (tlW p q) ((p : ℤ) * (q : ℤ)) (wordOf h) :=
    (levLe_iff_decor_belowE _ _ _).mpr ⟨hm, fun r hr => by
      have hr' := hh_mem.2 r hr
      rw [mem_winE] at hr'
      exact ⟨hr'.2.1, hr'.2.2.2⟩⟩
  refine (mem_loopsInE_iff (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ))) y).mpr
    ⟨lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n ++ wordOf h ++
      lpow (wordOf (tlLowTau p q hp hq hcop)) n, ?_, ?_, ?_⟩
  · -- the word represents `y`
    have h1 : FreeGroup.mk (lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n) =
        ((tlLowTau p q hp hq hcop)⁻¹) ^ n := by
      rw [mk_lpow, ← FreeGroup.inv_mk, mk_wordOf]
    have h2 : FreeGroup.mk (lpow (wordOf (tlLowTau p q hp hq hcop)) n) =
        (tlLowTau p q hp hq hcop) ^ n := by
      rw [mk_lpow, mk_wordOf]
    have h3 : FreeGroup.mk (wordOf h) = h := mk_wordOf h
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, h1, h2, h3, hy_eq, hkn]
    rw [zpow_neg_eq_inv_pow]
    rw [show (tlLowTau p q hp hq hcop) ^ n =
        (((tlLowTau p q hp hq hcop)⁻¹) ^ n)⁻¹ from by rw [inv_pow, inv_inv]]
  · -- it is a loop
    rw [CoedgeBase.lsig_append, CoedgeBase.lsig_append, lsig_lpow, lsig_lpow,
      CoedgeBase.lsig_invRev, hTlsig, hh_lsig]
    ring
  · -- all its edges lie in the lower half-plane
    have hlsigA : lsig (tlW p q)
        (lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n) = -(n : ℤ) := by
      rw [lsig_lpow, CoedgeBase.lsig_invRev, hTlsig]
      ring
    have hAB : levLe (tlW p q) ((p : ℤ) * (q : ℤ))
        (lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n ++ wordOf h) := by
      have hab : levLe (tlW p q) ((p : ℤ) * (q : ℤ) + n) (wordOf h) :=
        levLe_mono hh_levLe (by omega)
      refine levLe_append (A := lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n)
        (B := wordOf h) (invRev_lpow_levels hTband hTlsig n).1 ?_
      refine levLe_mono hab ?_
      rw [hlsigA]
      exact le_of_eq (by ring)
    have hABC : levLe (tlW p q) ((p : ℤ) * (q : ℤ))
        (lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n ++ wordOf h ++
          lpow (wordOf (tlLowTau p q hp hq hcop)) n) := by
      refine levLe_append (A := lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n
        ++ wordOf h) (B := lpow (wordOf (tlLowTau p q hp hq hcop)) n) hAB ?_
      have hC : levLe (tlW p q) ((p : ℤ) * (q : ℤ) + n)
          (lpow (wordOf (tlLowTau p q hp hq hcop)) n) :=
        levLe_mono (band_lpow_levels hTband hTlsig n).1 (le_of_eq (by ring))
      refine levLe_mono hC ?_
      rw [CoedgeBase.lsig_append, hlsigA, hh_lsig]
      exact le_of_eq (by ring)
    exact ((levLe_iff_decor_belowE _ _ _).mp hABC).2

/-- **The upper half `tlPge 0` is generated by loops of the half-plane `[0,∞)`.** -/
theorem tlPge_zero_le_aboveE (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    tlPge p q hp hq hcop Wt 0 ≤
      loopsInE (tlW p q) (aboveE (tlW p q) 0) := by
  have hTband := tlTau_band p q hp hq hcop
  have hTlsig := tlTau_lsig p q hp hq hcop
  have hH := tlH_eq_loopsInE (p := p) (q := q) (Wt := Wt) hp hq hcop hW0 hcoh hwin htree
  rw [tlPge]
  refine (Subgroup.closure_le (K := loopsInE (tlW p q) (aboveE (tlW p q) 0))).mpr ?_
  rintro y ⟨k, hk, hyk⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hkn : k = (n : ℤ) := by omega
  set h := (tlLowTau p q hp hq hcop) ^ (-k) * y * (tlLowTau p q hp hq hcop) ^ k with hh
  have hhH : h ∈ tlH p q Wt := (mem_tlHk_iff_local p q hp hq hcop Wt k y).mp hyk
  have hy_eq : y = (tlLowTau p q hp hq hcop) ^ k * h *
      ((tlLowTau p q hp hq hcop) ^ k)⁻¹ := by
    rw [hh]; group
  have hh_mem : h ∈ loopsInE (tlW p q) (winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) := by
    rw [← hH]; exact hhH
  have hh_lsig : lsig (tlW p q) (wordOf h) = 0 := by
    rw [CoedgeBase.lsig_wordOf, hh_mem.1]
    simp
  have hh_levGe : levGe (tlW p q) 0 (wordOf h) :=
    (levGe_iff_decor_aboveE _ _ _).mpr ⟨le_rfl, fun r hr => by
      have hr' := hh_mem.2 r hr
      rw [mem_winE] at hr'
      exact ⟨hr'.1, hr'.2.2.1⟩⟩
  refine (mem_loopsInE_iff (tlW p q) (aboveE (tlW p q) 0) y).mpr
    ⟨lpow (wordOf (tlLowTau p q hp hq hcop)) n ++ wordOf h ++
      lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n, ?_, ?_, ?_⟩
  · -- the word represents `y`
    have h1 : FreeGroup.mk (lpow (wordOf (tlLowTau p q hp hq hcop)) n) =
        (tlLowTau p q hp hq hcop) ^ n := by
      rw [mk_lpow, mk_wordOf]
    have h2 : FreeGroup.mk (lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n) =
        ((tlLowTau p q hp hq hcop)⁻¹) ^ n := by
      rw [mk_lpow, ← FreeGroup.inv_mk, mk_wordOf]
    have h3 : FreeGroup.mk (wordOf h) = h := mk_wordOf h
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, h1, h2, h3, hy_eq, hkn, inv_pow]
    group
  · -- it is a loop
    rw [CoedgeBase.lsig_append, CoedgeBase.lsig_append, lsig_lpow, lsig_lpow,
      CoedgeBase.lsig_invRev, hTlsig, hh_lsig]
    ring
  · -- all its edges lie in the upper half-plane
    have hlsigA : lsig (tlW p q) (lpow (wordOf (tlLowTau p q hp hq hcop)) n) = (n : ℤ) := by
      rw [lsig_lpow, hTlsig]; ring
    have hAB : levGe (tlW p q) 0
        (lpow (wordOf (tlLowTau p q hp hq hcop)) n ++ wordOf h) := by
      have hab : levGe (tlW p q) (-(n : ℤ)) (wordOf h) :=
        levGe_mono hh_levGe (by omega)
      refine levGe_append (A := lpow (wordOf (tlLowTau p q hp hq hcop)) n) (B := wordOf h)
        (band_lpow_levels hTband hTlsig n).2 ?_
      refine levGe_mono hab ?_
      rw [hlsigA]
      exact le_of_eq (by ring)
    have hABC : levGe (tlW p q) 0
        (lpow (wordOf (tlLowTau p q hp hq hcop)) n ++ wordOf h ++
          lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n) := by
      refine levGe_append (A := lpow (wordOf (tlLowTau p q hp hq hcop)) n ++ wordOf h)
        (B := lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n) hAB ?_
      have hC : levGe (tlW p q) (-(n : ℤ))
          (lpow (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) n) :=
        (invRev_lpow_levels hTband hTlsig n).2
      refine levGe_mono hC ?_
      rw [CoedgeBase.lsig_append, hlsigA, hh_lsig]
      exact le_of_eq (by ring)
    exact ((levGe_iff_decor_aboveE _ _ _).mp hABC).2

/-- **The downward shift**: conjugating a loop of the lower half-plane by `τ⁻¹` lowers the bound
by one. -/
theorem loopsInE_conj_tau_inv_belowE {x : FreeGroup (Fin 2)}
    (hx : x ∈ loopsInE (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ)))) :
    (tlLowTau p q hp hq hcop)⁻¹ * x * tlLowTau p q hp hq hcop ∈
      loopsInE (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ) - 1)) := by
  have hm : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) :=
    mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)
  have hTband := tlTau_band p q hp hq hcop
  have hTlsig := tlTau_lsig p q hp hq hcop
  have hx_lev : levLe (tlW p q) ((p : ℤ) * (q : ℤ)) (wordOf x) :=
    (levLe_iff_decor_belowE _ _ _).mpr ⟨hm, hx.2⟩
  have hx_lsig : lsig (tlW p q) (wordOf x) = 0 := by
    rw [CoedgeBase.lsig_wordOf, hx.1]
    simp
  refine (mem_loopsInE_iff _ _ _).mpr
    ⟨FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)) ++ wordOf x ++
      wordOf (tlLowTau p q hp hq hcop), ?_, ?_, ?_⟩
  · have hA : FreeGroup.mk (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) =
        (tlLowTau p q hp hq hcop)⁻¹ := by
      rw [← FreeGroup.inv_mk, mk_wordOf]
    have hB : FreeGroup.mk (wordOf x) = x := mk_wordOf x
    have hC : FreeGroup.mk (wordOf (tlLowTau p q hp hq hcop)) =
        tlLowTau p q hp hq hcop := mk_wordOf _
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, hA, hB, hC]
  · rw [CoedgeBase.lsig_append, CoedgeBase.lsig_append, CoedgeBase.lsig_invRev, hTlsig,
      hx_lsig]
    ring
  · have hlsigA : lsig (tlW p q) (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) = -1 := by
      rw [CoedgeBase.lsig_invRev, hTlsig]
    have hA : levLe (tlW p q) ((p : ℤ) * (q : ℤ) - 1)
        (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) := by
      have h := (invRev_levels (tlW p q) (wordOf (tlLowTau p q hp hq hcop))).1
        ((p : ℤ) * (q : ℤ)) (fun k hk => (hTband k hk).2)
      simpa [hTlsig] using h
    have hAB : levLe (tlW p q) ((p : ℤ) * (q : ℤ) - 1)
        (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)) ++ wordOf x) := by
      refine levLe_append (A := FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)))
        (B := wordOf x) hA ?_
      refine levLe_mono hx_lev ?_
      rw [hlsigA]
      exact le_of_eq (by ring)
    have hABC : levLe (tlW p q) ((p : ℤ) * (q : ℤ) - 1)
        (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)) ++ wordOf x ++
          wordOf (tlLowTau p q hp hq hcop)) := by
      refine levLe_append (A := FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)) ++ wordOf x)
        (B := wordOf (tlLowTau p q hp hq hcop)) hAB ?_
      refine levLe_mono (show levLe (tlW p q) ((p : ℤ) * (q : ℤ))
        (wordOf (tlLowTau p q hp hq hcop)) from fun j hj => (hTband j hj).2) ?_
      rw [CoedgeBase.lsig_append, hlsigA, hx_lsig]
      exact le_of_eq (by ring)
    exact ((levLe_iff_decor_belowE _ _ _).mp hABC).2

/-- **The upward shift**: conjugating a loop of the gate window by `τ` gives a loop of the band
vertex. -/
theorem loopsInE_conj_tau_winE {z : FreeGroup (Fin 2)}
    (hz : z ∈ loopsInE (tlW p q) (winE (tlW p q) 0 ((p : ℤ) * (q : ℤ) - 1))) :
    tlLowTau p q hp hq hcop * z * (tlLowTau p q hp hq hcop)⁻¹ ∈
      loopsInE (tlW p q) (winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) := by
  have hm : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) - 1 := by
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hTband := tlTau_band p q hp hq hcop
  have hTlsig := tlTau_lsig p q hp hq hcop
  have hz_lsig : lsig (tlW p q) (wordOf z) = 0 := by
    rw [CoedgeBase.lsig_wordOf, hz.1]
    simp
  have hz_levLe : levLe (tlW p q) ((p : ℤ) * (q : ℤ) - 1) (wordOf z) :=
    (levLe_iff_decor_belowE _ _ _).mpr ⟨hm, fun r hr => by
      have hr' := hz.2 r hr
      rw [mem_winE] at hr'
      exact ⟨hr'.2.1, hr'.2.2.2⟩⟩
  have hz_levGe : levGe (tlW p q) 0 (wordOf z) :=
    (levGe_iff_decor_aboveE _ _ _).mpr ⟨le_rfl, fun r hr => by
      have hr' := hz.2 r hr
      rw [mem_winE] at hr'
      exact ⟨hr'.1, hr'.2.2.1⟩⟩
  refine (mem_loopsInE_iff _ _ _).mpr
    ⟨wordOf (tlLowTau p q hp hq hcop) ++ wordOf z ++
      FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop)), ?_, ?_, ?_⟩
  · have hA : FreeGroup.mk (wordOf (tlLowTau p q hp hq hcop)) =
        tlLowTau p q hp hq hcop := mk_wordOf _
    have hB : FreeGroup.mk (wordOf z) = z := mk_wordOf z
    have hC : FreeGroup.mk (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) =
        (tlLowTau p q hp hq hcop)⁻¹ := by
      rw [← FreeGroup.inv_mk, mk_wordOf]
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, hA, hB, hC]
  · rw [CoedgeBase.lsig_append, CoedgeBase.lsig_append, CoedgeBase.lsig_invRev, hTlsig,
      hz_lsig]
    ring
  · refine winE_decor_of_band (tlW p q) 0 ((p : ℤ) * (q : ℤ)) _ ?_
    have hlsigA : lsig (tlW p q) (wordOf (tlLowTau p q hp hq hcop)) = 1 := hTlsig
    have hlsigC : lsig (tlW p q) (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) = -1 := by
      rw [CoedgeBase.lsig_invRev, hTlsig]
    have hC_le : levLe (tlW p q) ((p : ℤ) * (q : ℤ) - 1)
        (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) := by
      have h := (invRev_levels (tlW p q) (wordOf (tlLowTau p q hp hq hcop))).1
        ((p : ℤ) * (q : ℤ)) (fun k hk => (hTband k hk).2)
      simpa [hTlsig] using h
    have hC_ge : levGe (tlW p q) (-1)
        (FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) := by
      have h := (invRev_levels (tlW p q) (wordOf (tlLowTau p q hp hq hcop))).2 0
        (fun k hk => (hTband k hk).1)
      simpa [hTlsig] using h
    intro j hj
    constructor
    · -- lower bound
      have hAB : levGe (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop) ++ wordOf z) := by
        have hab : levGe (tlW p q) (-1) (wordOf z) := levGe_mono hz_levGe (by norm_num)
        refine levGe_append (A := wordOf (tlLowTau p q hp hq hcop)) (B := wordOf z)
          (fun k hk => (hTband k hk).1) ?_
        refine levGe_mono hab ?_
        rw [hlsigA]
        exact le_of_eq (by ring)
      have hABC : levGe (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop) ++ wordOf z ++
          FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) := by
        refine levGe_append (A := wordOf (tlLowTau p q hp hq hcop) ++ wordOf z)
          (B := FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) hAB ?_
        refine levGe_mono hC_ge ?_
        rw [CoedgeBase.lsig_append, hlsigA, hz_lsig]
        exact le_of_eq (by ring)
      exact hABC j hj
    · -- upper bound
      have hAB : levLe (tlW p q) ((p : ℤ) * (q : ℤ))
          (wordOf (tlLowTau p q hp hq hcop) ++ wordOf z) := by
        refine levLe_append (A := wordOf (tlLowTau p q hp hq hcop)) (B := wordOf z)
          (fun k hk => (hTband k hk).2) ?_
        refine levLe_mono hz_levLe ?_
        rw [hlsigA]
      have hABC : levLe (tlW p q) ((p : ℤ) * (q : ℤ))
          (wordOf (tlLowTau p q hp hq hcop) ++ wordOf z ++
            FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) := by
        refine levLe_append (A := wordOf (tlLowTau p q hp hq hcop) ++ wordOf z)
          (B := FreeGroup.invRev (wordOf (tlLowTau p q hp hq hcop))) hAB ?_
        refine levLe_mono hC_le ?_
        rw [CoedgeBase.lsig_append, hlsigA, hz_lsig]
        exact le_of_eq (by ring)
      exact hABC j hj

/-- **The intersection formula at `c = 0`.** -/
theorem band_halves_inter_zero (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    tlPle p q hp hq hcop Wt 0 ⊓ tlPge p q hp hq hcop Wt 1 =
      tlAk p q hp hq hcop Wt 0 := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxPle, hxPge⟩ := Subgroup.mem_inf.mp hx
    set z := (tlLowTau p q hp hq hcop)⁻¹ * x * tlLowTau p q hp hq hcop with hz
    have hz_ge : z ∈ tlPge p q hp hq hcop Wt 0 := by
      have h := tlPge_conj_le p q hp hq hcop Wt 1 (-1) hxPge
      rw [show (1 : ℤ) + -1 = (0 : ℤ) from by ring, Subgroup.mem_comap] at h
      convert h using 1
      rw [hz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hx_below : x ∈ loopsInE (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ))) :=
      tlPle_zero_le_belowE p q hp hq hcop Wt hW0 hcoh hwin htree hxPle
    have hz_below : z ∈ loopsInE (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ) - 1)) := by
      have h := loopsInE_conj_tau_inv_belowE p q hp hq hcop hx_below
      exact h
    have hz_above : z ∈ loopsInE (tlW p q) (aboveE (tlW p q) 0) :=
      tlPge_zero_le_aboveE p q hp hq hcop Wt hW0 hcoh hwin htree hz_ge
    have hz_mid : z ∈ loopsInE (tlW p q) (winE (tlW p q) 0 ((p : ℤ) * (q : ℤ) - 1)) := by
      have h1 : z ∈ loopsInE (tlW p q) (belowE (tlW p q) ((p : ℤ) * (q : ℤ) - 1)) ⊓
          loopsInE (tlW p q) (aboveE (tlW p q) 0) := ⟨hz_below, hz_above⟩
      rw [loopsInE_inf, belowE_inter_aboveE] at h1
      exact h1
    have hz_H : z ∈ tlH p q Wt := by
      rw [tlH_eq_loopsInE (p := p) (q := q) (Wt := Wt) hp hq hcop hW0 hcoh hwin htree]
      refine loopsInE_mono (fun e he => ?_) hz_mid
      rw [mem_winE] at he ⊢
      exact ⟨he.1, le_trans he.2.1 (by omega), he.2.2.1, le_trans he.2.2.2 (by omega)⟩
    have hx_H : x ∈ tlH p q Wt := by
      rw [tlH_eq_loopsInE (p := p) (q := q) (Wt := Wt) hp hq hcop hW0 hcoh hwin htree]
      have h := loopsInE_conj_tau_winE p q hp hq hcop hz_mid
      convert h using 1
      rw [hz]
      group
    have hx_conj : x ∈ tlHk p q hp hq hcop Wt 1 := by
      rw [mem_tlHk_iff_local]
      convert hz_H using 1
      rw [hz]
      simp only [zpow_neg_one, zpow_one]
    refine Subgroup.mem_inf.mpr ⟨?_, hx_conj⟩
    rw [mem_tlHk_iff_local]
    convert hx_H using 1
    simp
  · exact le_inf (tlAk_le_tlPle p q hp hq hcop Wt 0)
      (tlAk_le_tlPge p q hp hq hcop Wt 0)

end Band

theorem band_halves_inter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (c : ℤ) :
    Work.OROneRel.tlPle p q hp hq hcop Wt c ⊓ Work.OROneRel.tlPge p q hp hq hcop Wt (c + 1)
      = Work.OROneRel.tlAk p q hp hq hcop Wt c := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxPle, hxPge⟩ := Subgroup.mem_inf.mp hx
    set z := (tlLowTau p q hp hq hcop) ^ (-c) * x * (tlLowTau p q hp hq hcop) ^ c with hz
    have hzPle : z ∈ tlPle p q hp hq hcop Wt 0 := by
      have h := tlPle_conj_le p q hp hq hcop Wt c (-c) hxPle
      rw [show c + -c = (0 : ℤ) from by ring, Subgroup.mem_comap] at h
      convert h using 1
      rw [hz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hzPge : z ∈ tlPge p q hp hq hcop Wt 1 := by
      have h := tlPge_conj_le p q hp hq hcop Wt (c + 1) (-c) hxPge
      rw [show c + 1 + -c = (1 : ℤ) from by ring, Subgroup.mem_comap] at h
      convert h using 1
      rw [hz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hzAk : z ∈ tlAk p q hp hq hcop Wt 0 := by
      rw [← band_halves_inter_zero p q hp hq hcop Wt hW0 hcoh hwin htree]
      exact ⟨hzPle, hzPge⟩
    obtain ⟨hz0, hz1⟩ := Subgroup.mem_inf.mp hzAk
    have hx_eq : x = (MulAut.conj ((tlLowTau p q hp hq hcop) ^ c)) z := by
      rw [hz, MulAut.conj_apply]
      group
    rw [tlAk, Subgroup.mem_inf]
    constructor
    · have h := mem_tlHk_conj p q hp hq hcop Wt 0 c hz0
      rw [show (0 : ℤ) + c = c from by ring] at h
      rwa [hx_eq]
    · have h := mem_tlHk_conj p q hp hq hcop Wt 1 c hz1
      rw [show (1 : ℤ) + c = c + 1 from by ring] at h
      rwa [hx_eq]
  · exact le_inf (tlAk_le_tlPle p q hp hq hcop Wt c)
      (tlAk_le_tlPge p q hp hq hcop Wt c)

end Work.OROneRel
