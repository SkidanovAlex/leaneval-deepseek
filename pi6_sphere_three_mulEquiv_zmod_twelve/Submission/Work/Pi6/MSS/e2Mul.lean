import Mathlib
import Submission.Work.Pi6.MSS.assemble
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.e2Add
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.MSS.e2Defs
import Submission.Work.Pi6.MSS.e2Asm
import Submission.Work.Pi6.MSS.e2Col_exists
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.koszulBounded
import Submission.Work.Pi6.MSS.mixedComm
import Submission.Work.Pi6.MSS.e2Psi_bij
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

theorem e2Mul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (D : Work.Pi6.MSS.PagesData 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p)) :
    ∃ e2 : ∀ (s q : ℕ), s ≤ N → q ≤ N →
        ((Work.Pi6.MSS.mssSS 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) D).E 2
            ((s : ℤ), (q : ℤ)) ≅
          ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
            (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))),
      (∀ (s q s' q' : ℕ) (hs : s ≤ N) (hq : q ≤ N) (hs' : s' ≤ N) (hq' : q' ≤ N)
        (b : Work.Pi6.Coh 𝕜 B s) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
        (b' : Work.Pi6.Coh 𝕜 B s') (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q')
        (hss : s + s' ≤ N) (hqq : q + q' ≤ N),
        (Work.Pi6.MSS.mssSS 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) D).mul 2
            ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
            (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
            ((e2 s q hs hq).inv.hom (b ⊗ₜ f)) ((e2 s' q' hs' hq').inv.hom (b' ⊗ₜ f'))
          = ((-1 : 𝕜) ^ (q * s')) • (e2 (s + s') (q + q') (by omega) (by omega)).inv.hom
              ((Work.Pi6.cup 𝕜 B s s' b b') ⊗ₜ
                (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f'))) ∧
      (∀ (s : ℕ) (hs : s ≤ N) (b : Work.Pi6.Coh 𝕜 B s),
        ((Work.Pi6.MSS.mssSS 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) D).botTo (s : ℤ) s).hom
            ((e2 s 0 (by omega) (by omega)).inv.hom
              (b ⊗ₜ Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) = 0 ↔
          (Work.Pi6.cmap 𝕜 p s).hom b = 0) ∧
      (∀ (q : ℕ) (hq : q ≤ N) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
        (∃ e : Work.Pi6.Coh 𝕜 E q,
            (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
          ∃ z : (Work.Pi6.MSS.mssSS 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) D).E (q + 2) (0, (q : ℤ)),
            ((Work.Pi6.MSS.mssSS 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) D).colTo (q : ℤ) q).hom z =
              (e2 0 q (by omega) (by omega)).inv.hom (Work.Pi6.One.one 𝕜 B ⊗ₜ f)) := by
  classical
  refine e2Mul_of 𝕜 p e₀ N D (e2ColAll 𝕜 p e₀ N hfib hconn hfin)
    (e2ColAll_pageUnit 𝕜 p e₀ N hfib hconn hfin)
    (rowMap_pageUnit 𝕜 p) ?_ ?_ ?_ ?_
  · intro s q s' q' hss hqq b f b' f'
    exact koszulBounded 𝕜 E B p e₀ N hfib hconn hfin
      (fun s s' b b' => rowMap_mul_aux 𝕜 p
        (fun t => ker_clsB_le_ker_Rb 𝕜 p t) (fun t => clsB_range_top 𝕜 B t) s s' b b')
      (fun q q' hqq f f' => e2ColAll_mul 𝕜 p e₀ N hfib hconn hfin q q'
        (Nat.le_trans (Nat.le_add_right q q') hqq)
        (Nat.le_trans (Nat.le_add_left q' q) hqq) hqq f f')
      (fun s q _ b f => mc_mssMul_mixed 𝕜 E B p s q (by ext <;> simp) (by ext <;> simp)
        (e2ColAll 𝕜 p e₀ N hfib hconn hfin q f) (e2Row 𝕜 p s b))
      s q s' q' hss hqq b f b' f'
  · exact e2Psi_bij 𝕜 E B p e₀ N hfib hconn hfin
  · exact fun (q : ℕ) (hq : q ≤ N) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) =>
      e2ColAll_edge 𝕜 p e₀ N hfib hconn hfin q hq f
  · exact fun (s : ℕ) (b : Work.Pi6.Coh 𝕜 B s) =>
      rowMap_botIter 𝕜 p (fun t x hx => mssBotIter_mkQ 𝕜 p t x hx) s b

end Work.Pi6.MSS
