import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.IntervalCases

namespace Commons.NumberTheory.Lagarias

open Finset

set_option maxRecDepth 100000

/-!  Finite verification of `σ₁(n) ≤ 18/5 * n` on `1501 ≤ n ≤ 2000`. -/

@[simp] lemma sigma_bound_1501 : (ArithmeticFunction.sigma 1 1501 : ℕ) ≤ 5403 := by
  decide

@[simp] lemma sigma_bound_1502 : (ArithmeticFunction.sigma 1 1502 : ℕ) ≤ 5407 := by
  decide

@[simp] lemma sigma_bound_1503 : (ArithmeticFunction.sigma 1 1503 : ℕ) ≤ 5410 := by
  decide

@[simp] lemma sigma_bound_1504 : (ArithmeticFunction.sigma 1 1504 : ℕ) ≤ 5414 := by
  decide

@[simp] lemma sigma_bound_1505 : (ArithmeticFunction.sigma 1 1505 : ℕ) ≤ 5418 := by
  decide

@[simp] lemma sigma_bound_1506 : (ArithmeticFunction.sigma 1 1506 : ℕ) ≤ 5421 := by
  decide

@[simp] lemma sigma_bound_1507 : (ArithmeticFunction.sigma 1 1507 : ℕ) ≤ 5425 := by
  decide

@[simp] lemma sigma_bound_1508 : (ArithmeticFunction.sigma 1 1508 : ℕ) ≤ 5428 := by
  decide

@[simp] lemma sigma_bound_1509 : (ArithmeticFunction.sigma 1 1509 : ℕ) ≤ 5432 := by
  decide

@[simp] lemma sigma_bound_1510 : (ArithmeticFunction.sigma 1 1510 : ℕ) ≤ 5436 := by
  decide

@[simp] lemma sigma_bound_1511 : (ArithmeticFunction.sigma 1 1511 : ℕ) ≤ 5439 := by
  decide

@[simp] lemma sigma_bound_1512 : (ArithmeticFunction.sigma 1 1512 : ℕ) ≤ 5443 := by
  decide

@[simp] lemma sigma_bound_1513 : (ArithmeticFunction.sigma 1 1513 : ℕ) ≤ 5446 := by
  decide

@[simp] lemma sigma_bound_1514 : (ArithmeticFunction.sigma 1 1514 : ℕ) ≤ 5450 := by
  decide

@[simp] lemma sigma_bound_1515 : (ArithmeticFunction.sigma 1 1515 : ℕ) ≤ 5454 := by
  decide

@[simp] lemma sigma_bound_1516 : (ArithmeticFunction.sigma 1 1516 : ℕ) ≤ 5457 := by
  decide

@[simp] lemma sigma_bound_1517 : (ArithmeticFunction.sigma 1 1517 : ℕ) ≤ 5461 := by
  decide

@[simp] lemma sigma_bound_1518 : (ArithmeticFunction.sigma 1 1518 : ℕ) ≤ 5464 := by
  decide

@[simp] lemma sigma_bound_1519 : (ArithmeticFunction.sigma 1 1519 : ℕ) ≤ 5468 := by
  decide

@[simp] lemma sigma_bound_1520 : (ArithmeticFunction.sigma 1 1520 : ℕ) ≤ 5472 := by
  decide

@[simp] lemma sigma_bound_1521 : (ArithmeticFunction.sigma 1 1521 : ℕ) ≤ 5475 := by
  decide

@[simp] lemma sigma_bound_1522 : (ArithmeticFunction.sigma 1 1522 : ℕ) ≤ 5479 := by
  decide

@[simp] lemma sigma_bound_1523 : (ArithmeticFunction.sigma 1 1523 : ℕ) ≤ 5482 := by
  decide

@[simp] lemma sigma_bound_1524 : (ArithmeticFunction.sigma 1 1524 : ℕ) ≤ 5486 := by
  decide

@[simp] lemma sigma_bound_1525 : (ArithmeticFunction.sigma 1 1525 : ℕ) ≤ 5490 := by
  decide

@[simp] lemma sigma_bound_1526 : (ArithmeticFunction.sigma 1 1526 : ℕ) ≤ 5493 := by
  decide

@[simp] lemma sigma_bound_1527 : (ArithmeticFunction.sigma 1 1527 : ℕ) ≤ 5497 := by
  decide

@[simp] lemma sigma_bound_1528 : (ArithmeticFunction.sigma 1 1528 : ℕ) ≤ 5500 := by
  decide

@[simp] lemma sigma_bound_1529 : (ArithmeticFunction.sigma 1 1529 : ℕ) ≤ 5504 := by
  decide

@[simp] lemma sigma_bound_1530 : (ArithmeticFunction.sigma 1 1530 : ℕ) ≤ 5508 := by
  decide

@[simp] lemma sigma_bound_1531 : (ArithmeticFunction.sigma 1 1531 : ℕ) ≤ 5511 := by
  decide

@[simp] lemma sigma_bound_1532 : (ArithmeticFunction.sigma 1 1532 : ℕ) ≤ 5515 := by
  decide

@[simp] lemma sigma_bound_1533 : (ArithmeticFunction.sigma 1 1533 : ℕ) ≤ 5518 := by
  decide

@[simp] lemma sigma_bound_1534 : (ArithmeticFunction.sigma 1 1534 : ℕ) ≤ 5522 := by
  decide

@[simp] lemma sigma_bound_1535 : (ArithmeticFunction.sigma 1 1535 : ℕ) ≤ 5526 := by
  decide

@[simp] lemma sigma_bound_1536 : (ArithmeticFunction.sigma 1 1536 : ℕ) ≤ 5529 := by
  decide

@[simp] lemma sigma_bound_1537 : (ArithmeticFunction.sigma 1 1537 : ℕ) ≤ 5533 := by
  decide

@[simp] lemma sigma_bound_1538 : (ArithmeticFunction.sigma 1 1538 : ℕ) ≤ 5536 := by
  decide

@[simp] lemma sigma_bound_1539 : (ArithmeticFunction.sigma 1 1539 : ℕ) ≤ 5540 := by
  decide

@[simp] lemma sigma_bound_1540 : (ArithmeticFunction.sigma 1 1540 : ℕ) ≤ 5544 := by
  decide

@[simp] lemma sigma_bound_1541 : (ArithmeticFunction.sigma 1 1541 : ℕ) ≤ 5547 := by
  decide

@[simp] lemma sigma_bound_1542 : (ArithmeticFunction.sigma 1 1542 : ℕ) ≤ 5551 := by
  decide

@[simp] lemma sigma_bound_1543 : (ArithmeticFunction.sigma 1 1543 : ℕ) ≤ 5554 := by
  decide

@[simp] lemma sigma_bound_1544 : (ArithmeticFunction.sigma 1 1544 : ℕ) ≤ 5558 := by
  decide

@[simp] lemma sigma_bound_1545 : (ArithmeticFunction.sigma 1 1545 : ℕ) ≤ 5562 := by
  decide

@[simp] lemma sigma_bound_1546 : (ArithmeticFunction.sigma 1 1546 : ℕ) ≤ 5565 := by
  decide

@[simp] lemma sigma_bound_1547 : (ArithmeticFunction.sigma 1 1547 : ℕ) ≤ 5569 := by
  decide

@[simp] lemma sigma_bound_1548 : (ArithmeticFunction.sigma 1 1548 : ℕ) ≤ 5572 := by
  decide

@[simp] lemma sigma_bound_1549 : (ArithmeticFunction.sigma 1 1549 : ℕ) ≤ 5576 := by
  decide

@[simp] lemma sigma_bound_1550 : (ArithmeticFunction.sigma 1 1550 : ℕ) ≤ 5580 := by
  decide

@[simp] lemma sigma_bound_1551 : (ArithmeticFunction.sigma 1 1551 : ℕ) ≤ 5583 := by
  decide

@[simp] lemma sigma_bound_1552 : (ArithmeticFunction.sigma 1 1552 : ℕ) ≤ 5587 := by
  decide

@[simp] lemma sigma_bound_1553 : (ArithmeticFunction.sigma 1 1553 : ℕ) ≤ 5590 := by
  decide

@[simp] lemma sigma_bound_1554 : (ArithmeticFunction.sigma 1 1554 : ℕ) ≤ 5594 := by
  decide

@[simp] lemma sigma_bound_1555 : (ArithmeticFunction.sigma 1 1555 : ℕ) ≤ 5598 := by
  decide

@[simp] lemma sigma_bound_1556 : (ArithmeticFunction.sigma 1 1556 : ℕ) ≤ 5601 := by
  decide

@[simp] lemma sigma_bound_1557 : (ArithmeticFunction.sigma 1 1557 : ℕ) ≤ 5605 := by
  decide

@[simp] lemma sigma_bound_1558 : (ArithmeticFunction.sigma 1 1558 : ℕ) ≤ 5608 := by
  decide

@[simp] lemma sigma_bound_1559 : (ArithmeticFunction.sigma 1 1559 : ℕ) ≤ 5612 := by
  decide

@[simp] lemma sigma_bound_1560 : (ArithmeticFunction.sigma 1 1560 : ℕ) ≤ 5616 := by
  decide

@[simp] lemma sigma_bound_1561 : (ArithmeticFunction.sigma 1 1561 : ℕ) ≤ 5619 := by
  decide

@[simp] lemma sigma_bound_1562 : (ArithmeticFunction.sigma 1 1562 : ℕ) ≤ 5623 := by
  decide

@[simp] lemma sigma_bound_1563 : (ArithmeticFunction.sigma 1 1563 : ℕ) ≤ 5626 := by
  decide

@[simp] lemma sigma_bound_1564 : (ArithmeticFunction.sigma 1 1564 : ℕ) ≤ 5630 := by
  decide

@[simp] lemma sigma_bound_1565 : (ArithmeticFunction.sigma 1 1565 : ℕ) ≤ 5634 := by
  decide

@[simp] lemma sigma_bound_1566 : (ArithmeticFunction.sigma 1 1566 : ℕ) ≤ 5637 := by
  decide

@[simp] lemma sigma_bound_1567 : (ArithmeticFunction.sigma 1 1567 : ℕ) ≤ 5641 := by
  decide

@[simp] lemma sigma_bound_1568 : (ArithmeticFunction.sigma 1 1568 : ℕ) ≤ 5644 := by
  decide

@[simp] lemma sigma_bound_1569 : (ArithmeticFunction.sigma 1 1569 : ℕ) ≤ 5648 := by
  decide

@[simp] lemma sigma_bound_1570 : (ArithmeticFunction.sigma 1 1570 : ℕ) ≤ 5652 := by
  decide

@[simp] lemma sigma_bound_1571 : (ArithmeticFunction.sigma 1 1571 : ℕ) ≤ 5655 := by
  decide

@[simp] lemma sigma_bound_1572 : (ArithmeticFunction.sigma 1 1572 : ℕ) ≤ 5659 := by
  decide

@[simp] lemma sigma_bound_1573 : (ArithmeticFunction.sigma 1 1573 : ℕ) ≤ 5662 := by
  decide

@[simp] lemma sigma_bound_1574 : (ArithmeticFunction.sigma 1 1574 : ℕ) ≤ 5666 := by
  decide

@[simp] lemma sigma_bound_1575 : (ArithmeticFunction.sigma 1 1575 : ℕ) ≤ 5670 := by
  decide

@[simp] lemma sigma_bound_1576 : (ArithmeticFunction.sigma 1 1576 : ℕ) ≤ 5673 := by
  decide

@[simp] lemma sigma_bound_1577 : (ArithmeticFunction.sigma 1 1577 : ℕ) ≤ 5677 := by
  decide

@[simp] lemma sigma_bound_1578 : (ArithmeticFunction.sigma 1 1578 : ℕ) ≤ 5680 := by
  decide

@[simp] lemma sigma_bound_1579 : (ArithmeticFunction.sigma 1 1579 : ℕ) ≤ 5684 := by
  decide

@[simp] lemma sigma_bound_1580 : (ArithmeticFunction.sigma 1 1580 : ℕ) ≤ 5688 := by
  decide

@[simp] lemma sigma_bound_1581 : (ArithmeticFunction.sigma 1 1581 : ℕ) ≤ 5691 := by
  decide

@[simp] lemma sigma_bound_1582 : (ArithmeticFunction.sigma 1 1582 : ℕ) ≤ 5695 := by
  decide

@[simp] lemma sigma_bound_1583 : (ArithmeticFunction.sigma 1 1583 : ℕ) ≤ 5698 := by
  decide

@[simp] lemma sigma_bound_1584 : (ArithmeticFunction.sigma 1 1584 : ℕ) ≤ 5702 := by
  decide

@[simp] lemma sigma_bound_1585 : (ArithmeticFunction.sigma 1 1585 : ℕ) ≤ 5706 := by
  decide

@[simp] lemma sigma_bound_1586 : (ArithmeticFunction.sigma 1 1586 : ℕ) ≤ 5709 := by
  decide

@[simp] lemma sigma_bound_1587 : (ArithmeticFunction.sigma 1 1587 : ℕ) ≤ 5713 := by
  decide

@[simp] lemma sigma_bound_1588 : (ArithmeticFunction.sigma 1 1588 : ℕ) ≤ 5716 := by
  decide

@[simp] lemma sigma_bound_1589 : (ArithmeticFunction.sigma 1 1589 : ℕ) ≤ 5720 := by
  decide

@[simp] lemma sigma_bound_1590 : (ArithmeticFunction.sigma 1 1590 : ℕ) ≤ 5724 := by
  decide

@[simp] lemma sigma_bound_1591 : (ArithmeticFunction.sigma 1 1591 : ℕ) ≤ 5727 := by
  decide

@[simp] lemma sigma_bound_1592 : (ArithmeticFunction.sigma 1 1592 : ℕ) ≤ 5731 := by
  decide

@[simp] lemma sigma_bound_1593 : (ArithmeticFunction.sigma 1 1593 : ℕ) ≤ 5734 := by
  decide

@[simp] lemma sigma_bound_1594 : (ArithmeticFunction.sigma 1 1594 : ℕ) ≤ 5738 := by
  decide

@[simp] lemma sigma_bound_1595 : (ArithmeticFunction.sigma 1 1595 : ℕ) ≤ 5742 := by
  decide

@[simp] lemma sigma_bound_1596 : (ArithmeticFunction.sigma 1 1596 : ℕ) ≤ 5745 := by
  decide

@[simp] lemma sigma_bound_1597 : (ArithmeticFunction.sigma 1 1597 : ℕ) ≤ 5749 := by
  decide

@[simp] lemma sigma_bound_1598 : (ArithmeticFunction.sigma 1 1598 : ℕ) ≤ 5752 := by
  decide

@[simp] lemma sigma_bound_1599 : (ArithmeticFunction.sigma 1 1599 : ℕ) ≤ 5756 := by
  decide

@[simp] lemma sigma_bound_1600 : (ArithmeticFunction.sigma 1 1600 : ℕ) ≤ 5760 := by
  decide

@[simp] lemma sigma_bound_1601 : (ArithmeticFunction.sigma 1 1601 : ℕ) ≤ 5763 := by
  decide

@[simp] lemma sigma_bound_1602 : (ArithmeticFunction.sigma 1 1602 : ℕ) ≤ 5767 := by
  decide

@[simp] lemma sigma_bound_1603 : (ArithmeticFunction.sigma 1 1603 : ℕ) ≤ 5770 := by
  decide

@[simp] lemma sigma_bound_1604 : (ArithmeticFunction.sigma 1 1604 : ℕ) ≤ 5774 := by
  decide

@[simp] lemma sigma_bound_1605 : (ArithmeticFunction.sigma 1 1605 : ℕ) ≤ 5778 := by
  decide

@[simp] lemma sigma_bound_1606 : (ArithmeticFunction.sigma 1 1606 : ℕ) ≤ 5781 := by
  decide

@[simp] lemma sigma_bound_1607 : (ArithmeticFunction.sigma 1 1607 : ℕ) ≤ 5785 := by
  decide

@[simp] lemma sigma_bound_1608 : (ArithmeticFunction.sigma 1 1608 : ℕ) ≤ 5788 := by
  decide

@[simp] lemma sigma_bound_1609 : (ArithmeticFunction.sigma 1 1609 : ℕ) ≤ 5792 := by
  decide

@[simp] lemma sigma_bound_1610 : (ArithmeticFunction.sigma 1 1610 : ℕ) ≤ 5796 := by
  decide

@[simp] lemma sigma_bound_1611 : (ArithmeticFunction.sigma 1 1611 : ℕ) ≤ 5799 := by
  decide

@[simp] lemma sigma_bound_1612 : (ArithmeticFunction.sigma 1 1612 : ℕ) ≤ 5803 := by
  decide

@[simp] lemma sigma_bound_1613 : (ArithmeticFunction.sigma 1 1613 : ℕ) ≤ 5806 := by
  decide

@[simp] lemma sigma_bound_1614 : (ArithmeticFunction.sigma 1 1614 : ℕ) ≤ 5810 := by
  decide

@[simp] lemma sigma_bound_1615 : (ArithmeticFunction.sigma 1 1615 : ℕ) ≤ 5814 := by
  decide

@[simp] lemma sigma_bound_1616 : (ArithmeticFunction.sigma 1 1616 : ℕ) ≤ 5817 := by
  decide

@[simp] lemma sigma_bound_1617 : (ArithmeticFunction.sigma 1 1617 : ℕ) ≤ 5821 := by
  decide

@[simp] lemma sigma_bound_1618 : (ArithmeticFunction.sigma 1 1618 : ℕ) ≤ 5824 := by
  decide

@[simp] lemma sigma_bound_1619 : (ArithmeticFunction.sigma 1 1619 : ℕ) ≤ 5828 := by
  decide

@[simp] lemma sigma_bound_1620 : (ArithmeticFunction.sigma 1 1620 : ℕ) ≤ 5832 := by
  decide

@[simp] lemma sigma_bound_1621 : (ArithmeticFunction.sigma 1 1621 : ℕ) ≤ 5835 := by
  decide

@[simp] lemma sigma_bound_1622 : (ArithmeticFunction.sigma 1 1622 : ℕ) ≤ 5839 := by
  decide

@[simp] lemma sigma_bound_1623 : (ArithmeticFunction.sigma 1 1623 : ℕ) ≤ 5842 := by
  decide

@[simp] lemma sigma_bound_1624 : (ArithmeticFunction.sigma 1 1624 : ℕ) ≤ 5846 := by
  decide

@[simp] lemma sigma_bound_1625 : (ArithmeticFunction.sigma 1 1625 : ℕ) ≤ 5850 := by
  decide

@[simp] lemma sigma_bound_1626 : (ArithmeticFunction.sigma 1 1626 : ℕ) ≤ 5853 := by
  decide

@[simp] lemma sigma_bound_1627 : (ArithmeticFunction.sigma 1 1627 : ℕ) ≤ 5857 := by
  decide

@[simp] lemma sigma_bound_1628 : (ArithmeticFunction.sigma 1 1628 : ℕ) ≤ 5860 := by
  decide

@[simp] lemma sigma_bound_1629 : (ArithmeticFunction.sigma 1 1629 : ℕ) ≤ 5864 := by
  decide

@[simp] lemma sigma_bound_1630 : (ArithmeticFunction.sigma 1 1630 : ℕ) ≤ 5868 := by
  decide

@[simp] lemma sigma_bound_1631 : (ArithmeticFunction.sigma 1 1631 : ℕ) ≤ 5871 := by
  decide

@[simp] lemma sigma_bound_1632 : (ArithmeticFunction.sigma 1 1632 : ℕ) ≤ 5875 := by
  decide

@[simp] lemma sigma_bound_1633 : (ArithmeticFunction.sigma 1 1633 : ℕ) ≤ 5878 := by
  decide

@[simp] lemma sigma_bound_1634 : (ArithmeticFunction.sigma 1 1634 : ℕ) ≤ 5882 := by
  decide

@[simp] lemma sigma_bound_1635 : (ArithmeticFunction.sigma 1 1635 : ℕ) ≤ 5886 := by
  decide

@[simp] lemma sigma_bound_1636 : (ArithmeticFunction.sigma 1 1636 : ℕ) ≤ 5889 := by
  decide

@[simp] lemma sigma_bound_1637 : (ArithmeticFunction.sigma 1 1637 : ℕ) ≤ 5893 := by
  decide

@[simp] lemma sigma_bound_1638 : (ArithmeticFunction.sigma 1 1638 : ℕ) ≤ 5896 := by
  decide

@[simp] lemma sigma_bound_1639 : (ArithmeticFunction.sigma 1 1639 : ℕ) ≤ 5900 := by
  decide

@[simp] lemma sigma_bound_1640 : (ArithmeticFunction.sigma 1 1640 : ℕ) ≤ 5904 := by
  decide

@[simp] lemma sigma_bound_1641 : (ArithmeticFunction.sigma 1 1641 : ℕ) ≤ 5907 := by
  decide

@[simp] lemma sigma_bound_1642 : (ArithmeticFunction.sigma 1 1642 : ℕ) ≤ 5911 := by
  decide

@[simp] lemma sigma_bound_1643 : (ArithmeticFunction.sigma 1 1643 : ℕ) ≤ 5914 := by
  decide

@[simp] lemma sigma_bound_1644 : (ArithmeticFunction.sigma 1 1644 : ℕ) ≤ 5918 := by
  decide

@[simp] lemma sigma_bound_1645 : (ArithmeticFunction.sigma 1 1645 : ℕ) ≤ 5922 := by
  decide

@[simp] lemma sigma_bound_1646 : (ArithmeticFunction.sigma 1 1646 : ℕ) ≤ 5925 := by
  decide

@[simp] lemma sigma_bound_1647 : (ArithmeticFunction.sigma 1 1647 : ℕ) ≤ 5929 := by
  decide

@[simp] lemma sigma_bound_1648 : (ArithmeticFunction.sigma 1 1648 : ℕ) ≤ 5932 := by
  decide

@[simp] lemma sigma_bound_1649 : (ArithmeticFunction.sigma 1 1649 : ℕ) ≤ 5936 := by
  decide

@[simp] lemma sigma_bound_1650 : (ArithmeticFunction.sigma 1 1650 : ℕ) ≤ 5940 := by
  decide

@[simp] lemma sigma_bound_1651 : (ArithmeticFunction.sigma 1 1651 : ℕ) ≤ 5943 := by
  decide

@[simp] lemma sigma_bound_1652 : (ArithmeticFunction.sigma 1 1652 : ℕ) ≤ 5947 := by
  decide

@[simp] lemma sigma_bound_1653 : (ArithmeticFunction.sigma 1 1653 : ℕ) ≤ 5950 := by
  decide

@[simp] lemma sigma_bound_1654 : (ArithmeticFunction.sigma 1 1654 : ℕ) ≤ 5954 := by
  decide

@[simp] lemma sigma_bound_1655 : (ArithmeticFunction.sigma 1 1655 : ℕ) ≤ 5958 := by
  decide

@[simp] lemma sigma_bound_1656 : (ArithmeticFunction.sigma 1 1656 : ℕ) ≤ 5961 := by
  decide

@[simp] lemma sigma_bound_1657 : (ArithmeticFunction.sigma 1 1657 : ℕ) ≤ 5965 := by
  decide

@[simp] lemma sigma_bound_1658 : (ArithmeticFunction.sigma 1 1658 : ℕ) ≤ 5968 := by
  decide

@[simp] lemma sigma_bound_1659 : (ArithmeticFunction.sigma 1 1659 : ℕ) ≤ 5972 := by
  decide

@[simp] lemma sigma_bound_1660 : (ArithmeticFunction.sigma 1 1660 : ℕ) ≤ 5976 := by
  decide

@[simp] lemma sigma_bound_1661 : (ArithmeticFunction.sigma 1 1661 : ℕ) ≤ 5979 := by
  decide

@[simp] lemma sigma_bound_1662 : (ArithmeticFunction.sigma 1 1662 : ℕ) ≤ 5983 := by
  decide

@[simp] lemma sigma_bound_1663 : (ArithmeticFunction.sigma 1 1663 : ℕ) ≤ 5986 := by
  decide

@[simp] lemma sigma_bound_1664 : (ArithmeticFunction.sigma 1 1664 : ℕ) ≤ 5990 := by
  decide

@[simp] lemma sigma_bound_1665 : (ArithmeticFunction.sigma 1 1665 : ℕ) ≤ 5994 := by
  decide

@[simp] lemma sigma_bound_1666 : (ArithmeticFunction.sigma 1 1666 : ℕ) ≤ 5997 := by
  decide

@[simp] lemma sigma_bound_1667 : (ArithmeticFunction.sigma 1 1667 : ℕ) ≤ 6001 := by
  decide

@[simp] lemma sigma_bound_1668 : (ArithmeticFunction.sigma 1 1668 : ℕ) ≤ 6004 := by
  decide

@[simp] lemma sigma_bound_1669 : (ArithmeticFunction.sigma 1 1669 : ℕ) ≤ 6008 := by
  decide

@[simp] lemma sigma_bound_1670 : (ArithmeticFunction.sigma 1 1670 : ℕ) ≤ 6012 := by
  decide

@[simp] lemma sigma_bound_1671 : (ArithmeticFunction.sigma 1 1671 : ℕ) ≤ 6015 := by
  decide

@[simp] lemma sigma_bound_1672 : (ArithmeticFunction.sigma 1 1672 : ℕ) ≤ 6019 := by
  decide

@[simp] lemma sigma_bound_1673 : (ArithmeticFunction.sigma 1 1673 : ℕ) ≤ 6022 := by
  decide

@[simp] lemma sigma_bound_1674 : (ArithmeticFunction.sigma 1 1674 : ℕ) ≤ 6026 := by
  decide

@[simp] lemma sigma_bound_1675 : (ArithmeticFunction.sigma 1 1675 : ℕ) ≤ 6030 := by
  decide

@[simp] lemma sigma_bound_1676 : (ArithmeticFunction.sigma 1 1676 : ℕ) ≤ 6033 := by
  decide

@[simp] lemma sigma_bound_1677 : (ArithmeticFunction.sigma 1 1677 : ℕ) ≤ 6037 := by
  decide

@[simp] lemma sigma_bound_1678 : (ArithmeticFunction.sigma 1 1678 : ℕ) ≤ 6040 := by
  decide

@[simp] lemma sigma_bound_1679 : (ArithmeticFunction.sigma 1 1679 : ℕ) ≤ 6044 := by
  decide

@[simp] lemma sigma_bound_1680 : (ArithmeticFunction.sigma 1 1680 : ℕ) ≤ 6048 := by
  decide

@[simp] lemma sigma_bound_1681 : (ArithmeticFunction.sigma 1 1681 : ℕ) ≤ 6051 := by
  decide

@[simp] lemma sigma_bound_1682 : (ArithmeticFunction.sigma 1 1682 : ℕ) ≤ 6055 := by
  decide

@[simp] lemma sigma_bound_1683 : (ArithmeticFunction.sigma 1 1683 : ℕ) ≤ 6058 := by
  decide

@[simp] lemma sigma_bound_1684 : (ArithmeticFunction.sigma 1 1684 : ℕ) ≤ 6062 := by
  decide

@[simp] lemma sigma_bound_1685 : (ArithmeticFunction.sigma 1 1685 : ℕ) ≤ 6066 := by
  decide

@[simp] lemma sigma_bound_1686 : (ArithmeticFunction.sigma 1 1686 : ℕ) ≤ 6069 := by
  decide

@[simp] lemma sigma_bound_1687 : (ArithmeticFunction.sigma 1 1687 : ℕ) ≤ 6073 := by
  decide

@[simp] lemma sigma_bound_1688 : (ArithmeticFunction.sigma 1 1688 : ℕ) ≤ 6076 := by
  decide

@[simp] lemma sigma_bound_1689 : (ArithmeticFunction.sigma 1 1689 : ℕ) ≤ 6080 := by
  decide

@[simp] lemma sigma_bound_1690 : (ArithmeticFunction.sigma 1 1690 : ℕ) ≤ 6084 := by
  decide

@[simp] lemma sigma_bound_1691 : (ArithmeticFunction.sigma 1 1691 : ℕ) ≤ 6087 := by
  decide

@[simp] lemma sigma_bound_1692 : (ArithmeticFunction.sigma 1 1692 : ℕ) ≤ 6091 := by
  decide

@[simp] lemma sigma_bound_1693 : (ArithmeticFunction.sigma 1 1693 : ℕ) ≤ 6094 := by
  decide

@[simp] lemma sigma_bound_1694 : (ArithmeticFunction.sigma 1 1694 : ℕ) ≤ 6098 := by
  decide

@[simp] lemma sigma_bound_1695 : (ArithmeticFunction.sigma 1 1695 : ℕ) ≤ 6102 := by
  decide

@[simp] lemma sigma_bound_1696 : (ArithmeticFunction.sigma 1 1696 : ℕ) ≤ 6105 := by
  decide

@[simp] lemma sigma_bound_1697 : (ArithmeticFunction.sigma 1 1697 : ℕ) ≤ 6109 := by
  decide

@[simp] lemma sigma_bound_1698 : (ArithmeticFunction.sigma 1 1698 : ℕ) ≤ 6112 := by
  decide

@[simp] lemma sigma_bound_1699 : (ArithmeticFunction.sigma 1 1699 : ℕ) ≤ 6116 := by
  decide

@[simp] lemma sigma_bound_1700 : (ArithmeticFunction.sigma 1 1700 : ℕ) ≤ 6120 := by
  decide

@[simp] lemma sigma_bound_1701 : (ArithmeticFunction.sigma 1 1701 : ℕ) ≤ 6123 := by
  decide

@[simp] lemma sigma_bound_1702 : (ArithmeticFunction.sigma 1 1702 : ℕ) ≤ 6127 := by
  decide

@[simp] lemma sigma_bound_1703 : (ArithmeticFunction.sigma 1 1703 : ℕ) ≤ 6130 := by
  decide

@[simp] lemma sigma_bound_1704 : (ArithmeticFunction.sigma 1 1704 : ℕ) ≤ 6134 := by
  decide

@[simp] lemma sigma_bound_1705 : (ArithmeticFunction.sigma 1 1705 : ℕ) ≤ 6138 := by
  decide

@[simp] lemma sigma_bound_1706 : (ArithmeticFunction.sigma 1 1706 : ℕ) ≤ 6141 := by
  decide

@[simp] lemma sigma_bound_1707 : (ArithmeticFunction.sigma 1 1707 : ℕ) ≤ 6145 := by
  decide

@[simp] lemma sigma_bound_1708 : (ArithmeticFunction.sigma 1 1708 : ℕ) ≤ 6148 := by
  decide

@[simp] lemma sigma_bound_1709 : (ArithmeticFunction.sigma 1 1709 : ℕ) ≤ 6152 := by
  decide

@[simp] lemma sigma_bound_1710 : (ArithmeticFunction.sigma 1 1710 : ℕ) ≤ 6156 := by
  decide

@[simp] lemma sigma_bound_1711 : (ArithmeticFunction.sigma 1 1711 : ℕ) ≤ 6159 := by
  decide

@[simp] lemma sigma_bound_1712 : (ArithmeticFunction.sigma 1 1712 : ℕ) ≤ 6163 := by
  decide

@[simp] lemma sigma_bound_1713 : (ArithmeticFunction.sigma 1 1713 : ℕ) ≤ 6166 := by
  decide

@[simp] lemma sigma_bound_1714 : (ArithmeticFunction.sigma 1 1714 : ℕ) ≤ 6170 := by
  decide

@[simp] lemma sigma_bound_1715 : (ArithmeticFunction.sigma 1 1715 : ℕ) ≤ 6174 := by
  decide

@[simp] lemma sigma_bound_1716 : (ArithmeticFunction.sigma 1 1716 : ℕ) ≤ 6177 := by
  decide

@[simp] lemma sigma_bound_1717 : (ArithmeticFunction.sigma 1 1717 : ℕ) ≤ 6181 := by
  decide

@[simp] lemma sigma_bound_1718 : (ArithmeticFunction.sigma 1 1718 : ℕ) ≤ 6184 := by
  decide

@[simp] lemma sigma_bound_1719 : (ArithmeticFunction.sigma 1 1719 : ℕ) ≤ 6188 := by
  decide

@[simp] lemma sigma_bound_1720 : (ArithmeticFunction.sigma 1 1720 : ℕ) ≤ 6192 := by
  decide

@[simp] lemma sigma_bound_1721 : (ArithmeticFunction.sigma 1 1721 : ℕ) ≤ 6195 := by
  decide

@[simp] lemma sigma_bound_1722 : (ArithmeticFunction.sigma 1 1722 : ℕ) ≤ 6199 := by
  decide

@[simp] lemma sigma_bound_1723 : (ArithmeticFunction.sigma 1 1723 : ℕ) ≤ 6202 := by
  decide

@[simp] lemma sigma_bound_1724 : (ArithmeticFunction.sigma 1 1724 : ℕ) ≤ 6206 := by
  decide

@[simp] lemma sigma_bound_1725 : (ArithmeticFunction.sigma 1 1725 : ℕ) ≤ 6210 := by
  decide

@[simp] lemma sigma_bound_1726 : (ArithmeticFunction.sigma 1 1726 : ℕ) ≤ 6213 := by
  decide

@[simp] lemma sigma_bound_1727 : (ArithmeticFunction.sigma 1 1727 : ℕ) ≤ 6217 := by
  decide

@[simp] lemma sigma_bound_1728 : (ArithmeticFunction.sigma 1 1728 : ℕ) ≤ 6220 := by
  decide

@[simp] lemma sigma_bound_1729 : (ArithmeticFunction.sigma 1 1729 : ℕ) ≤ 6224 := by
  decide

@[simp] lemma sigma_bound_1730 : (ArithmeticFunction.sigma 1 1730 : ℕ) ≤ 6228 := by
  decide

@[simp] lemma sigma_bound_1731 : (ArithmeticFunction.sigma 1 1731 : ℕ) ≤ 6231 := by
  decide

@[simp] lemma sigma_bound_1732 : (ArithmeticFunction.sigma 1 1732 : ℕ) ≤ 6235 := by
  decide

@[simp] lemma sigma_bound_1733 : (ArithmeticFunction.sigma 1 1733 : ℕ) ≤ 6238 := by
  decide

@[simp] lemma sigma_bound_1734 : (ArithmeticFunction.sigma 1 1734 : ℕ) ≤ 6242 := by
  decide

@[simp] lemma sigma_bound_1735 : (ArithmeticFunction.sigma 1 1735 : ℕ) ≤ 6246 := by
  decide

@[simp] lemma sigma_bound_1736 : (ArithmeticFunction.sigma 1 1736 : ℕ) ≤ 6249 := by
  decide

@[simp] lemma sigma_bound_1737 : (ArithmeticFunction.sigma 1 1737 : ℕ) ≤ 6253 := by
  decide

@[simp] lemma sigma_bound_1738 : (ArithmeticFunction.sigma 1 1738 : ℕ) ≤ 6256 := by
  decide

@[simp] lemma sigma_bound_1739 : (ArithmeticFunction.sigma 1 1739 : ℕ) ≤ 6260 := by
  decide

@[simp] lemma sigma_bound_1740 : (ArithmeticFunction.sigma 1 1740 : ℕ) ≤ 6264 := by
  decide

@[simp] lemma sigma_bound_1741 : (ArithmeticFunction.sigma 1 1741 : ℕ) ≤ 6267 := by
  decide

@[simp] lemma sigma_bound_1742 : (ArithmeticFunction.sigma 1 1742 : ℕ) ≤ 6271 := by
  decide

@[simp] lemma sigma_bound_1743 : (ArithmeticFunction.sigma 1 1743 : ℕ) ≤ 6274 := by
  decide

@[simp] lemma sigma_bound_1744 : (ArithmeticFunction.sigma 1 1744 : ℕ) ≤ 6278 := by
  decide

@[simp] lemma sigma_bound_1745 : (ArithmeticFunction.sigma 1 1745 : ℕ) ≤ 6282 := by
  decide

@[simp] lemma sigma_bound_1746 : (ArithmeticFunction.sigma 1 1746 : ℕ) ≤ 6285 := by
  decide

@[simp] lemma sigma_bound_1747 : (ArithmeticFunction.sigma 1 1747 : ℕ) ≤ 6289 := by
  decide

@[simp] lemma sigma_bound_1748 : (ArithmeticFunction.sigma 1 1748 : ℕ) ≤ 6292 := by
  decide

@[simp] lemma sigma_bound_1749 : (ArithmeticFunction.sigma 1 1749 : ℕ) ≤ 6296 := by
  decide

@[simp] lemma sigma_bound_1750 : (ArithmeticFunction.sigma 1 1750 : ℕ) ≤ 6300 := by
  decide

@[simp] lemma sigma_bound_1751 : (ArithmeticFunction.sigma 1 1751 : ℕ) ≤ 6303 := by
  decide

@[simp] lemma sigma_bound_1752 : (ArithmeticFunction.sigma 1 1752 : ℕ) ≤ 6307 := by
  decide

@[simp] lemma sigma_bound_1753 : (ArithmeticFunction.sigma 1 1753 : ℕ) ≤ 6310 := by
  decide

@[simp] lemma sigma_bound_1754 : (ArithmeticFunction.sigma 1 1754 : ℕ) ≤ 6314 := by
  decide

@[simp] lemma sigma_bound_1755 : (ArithmeticFunction.sigma 1 1755 : ℕ) ≤ 6318 := by
  decide

@[simp] lemma sigma_bound_1756 : (ArithmeticFunction.sigma 1 1756 : ℕ) ≤ 6321 := by
  decide

@[simp] lemma sigma_bound_1757 : (ArithmeticFunction.sigma 1 1757 : ℕ) ≤ 6325 := by
  decide

@[simp] lemma sigma_bound_1758 : (ArithmeticFunction.sigma 1 1758 : ℕ) ≤ 6328 := by
  decide

@[simp] lemma sigma_bound_1759 : (ArithmeticFunction.sigma 1 1759 : ℕ) ≤ 6332 := by
  decide

@[simp] lemma sigma_bound_1760 : (ArithmeticFunction.sigma 1 1760 : ℕ) ≤ 6336 := by
  decide

@[simp] lemma sigma_bound_1761 : (ArithmeticFunction.sigma 1 1761 : ℕ) ≤ 6339 := by
  decide

@[simp] lemma sigma_bound_1762 : (ArithmeticFunction.sigma 1 1762 : ℕ) ≤ 6343 := by
  decide

@[simp] lemma sigma_bound_1763 : (ArithmeticFunction.sigma 1 1763 : ℕ) ≤ 6346 := by
  decide

@[simp] lemma sigma_bound_1764 : (ArithmeticFunction.sigma 1 1764 : ℕ) ≤ 6350 := by
  decide

@[simp] lemma sigma_bound_1765 : (ArithmeticFunction.sigma 1 1765 : ℕ) ≤ 6354 := by
  decide

@[simp] lemma sigma_bound_1766 : (ArithmeticFunction.sigma 1 1766 : ℕ) ≤ 6357 := by
  decide

@[simp] lemma sigma_bound_1767 : (ArithmeticFunction.sigma 1 1767 : ℕ) ≤ 6361 := by
  decide

@[simp] lemma sigma_bound_1768 : (ArithmeticFunction.sigma 1 1768 : ℕ) ≤ 6364 := by
  decide

@[simp] lemma sigma_bound_1769 : (ArithmeticFunction.sigma 1 1769 : ℕ) ≤ 6368 := by
  decide

@[simp] lemma sigma_bound_1770 : (ArithmeticFunction.sigma 1 1770 : ℕ) ≤ 6372 := by
  decide

@[simp] lemma sigma_bound_1771 : (ArithmeticFunction.sigma 1 1771 : ℕ) ≤ 6375 := by
  decide

@[simp] lemma sigma_bound_1772 : (ArithmeticFunction.sigma 1 1772 : ℕ) ≤ 6379 := by
  decide

@[simp] lemma sigma_bound_1773 : (ArithmeticFunction.sigma 1 1773 : ℕ) ≤ 6382 := by
  decide

@[simp] lemma sigma_bound_1774 : (ArithmeticFunction.sigma 1 1774 : ℕ) ≤ 6386 := by
  decide

@[simp] lemma sigma_bound_1775 : (ArithmeticFunction.sigma 1 1775 : ℕ) ≤ 6390 := by
  decide

@[simp] lemma sigma_bound_1776 : (ArithmeticFunction.sigma 1 1776 : ℕ) ≤ 6393 := by
  decide

@[simp] lemma sigma_bound_1777 : (ArithmeticFunction.sigma 1 1777 : ℕ) ≤ 6397 := by
  decide

@[simp] lemma sigma_bound_1778 : (ArithmeticFunction.sigma 1 1778 : ℕ) ≤ 6400 := by
  decide

@[simp] lemma sigma_bound_1779 : (ArithmeticFunction.sigma 1 1779 : ℕ) ≤ 6404 := by
  decide

@[simp] lemma sigma_bound_1780 : (ArithmeticFunction.sigma 1 1780 : ℕ) ≤ 6408 := by
  decide

@[simp] lemma sigma_bound_1781 : (ArithmeticFunction.sigma 1 1781 : ℕ) ≤ 6411 := by
  decide

@[simp] lemma sigma_bound_1782 : (ArithmeticFunction.sigma 1 1782 : ℕ) ≤ 6415 := by
  decide

@[simp] lemma sigma_bound_1783 : (ArithmeticFunction.sigma 1 1783 : ℕ) ≤ 6418 := by
  decide

@[simp] lemma sigma_bound_1784 : (ArithmeticFunction.sigma 1 1784 : ℕ) ≤ 6422 := by
  decide

@[simp] lemma sigma_bound_1785 : (ArithmeticFunction.sigma 1 1785 : ℕ) ≤ 6426 := by
  decide

@[simp] lemma sigma_bound_1786 : (ArithmeticFunction.sigma 1 1786 : ℕ) ≤ 6429 := by
  decide

@[simp] lemma sigma_bound_1787 : (ArithmeticFunction.sigma 1 1787 : ℕ) ≤ 6433 := by
  decide

@[simp] lemma sigma_bound_1788 : (ArithmeticFunction.sigma 1 1788 : ℕ) ≤ 6436 := by
  decide

@[simp] lemma sigma_bound_1789 : (ArithmeticFunction.sigma 1 1789 : ℕ) ≤ 6440 := by
  decide

@[simp] lemma sigma_bound_1790 : (ArithmeticFunction.sigma 1 1790 : ℕ) ≤ 6444 := by
  decide

@[simp] lemma sigma_bound_1791 : (ArithmeticFunction.sigma 1 1791 : ℕ) ≤ 6447 := by
  decide

@[simp] lemma sigma_bound_1792 : (ArithmeticFunction.sigma 1 1792 : ℕ) ≤ 6451 := by
  decide

@[simp] lemma sigma_bound_1793 : (ArithmeticFunction.sigma 1 1793 : ℕ) ≤ 6454 := by
  decide

@[simp] lemma sigma_bound_1794 : (ArithmeticFunction.sigma 1 1794 : ℕ) ≤ 6458 := by
  decide

@[simp] lemma sigma_bound_1795 : (ArithmeticFunction.sigma 1 1795 : ℕ) ≤ 6462 := by
  decide

@[simp] lemma sigma_bound_1796 : (ArithmeticFunction.sigma 1 1796 : ℕ) ≤ 6465 := by
  decide

@[simp] lemma sigma_bound_1797 : (ArithmeticFunction.sigma 1 1797 : ℕ) ≤ 6469 := by
  decide

@[simp] lemma sigma_bound_1798 : (ArithmeticFunction.sigma 1 1798 : ℕ) ≤ 6472 := by
  decide

@[simp] lemma sigma_bound_1799 : (ArithmeticFunction.sigma 1 1799 : ℕ) ≤ 6476 := by
  decide

@[simp] lemma sigma_bound_1800 : (ArithmeticFunction.sigma 1 1800 : ℕ) ≤ 6480 := by
  decide

@[simp] lemma sigma_bound_1801 : (ArithmeticFunction.sigma 1 1801 : ℕ) ≤ 6483 := by
  decide

@[simp] lemma sigma_bound_1802 : (ArithmeticFunction.sigma 1 1802 : ℕ) ≤ 6487 := by
  decide

@[simp] lemma sigma_bound_1803 : (ArithmeticFunction.sigma 1 1803 : ℕ) ≤ 6490 := by
  decide

@[simp] lemma sigma_bound_1804 : (ArithmeticFunction.sigma 1 1804 : ℕ) ≤ 6494 := by
  decide

@[simp] lemma sigma_bound_1805 : (ArithmeticFunction.sigma 1 1805 : ℕ) ≤ 6498 := by
  decide

@[simp] lemma sigma_bound_1806 : (ArithmeticFunction.sigma 1 1806 : ℕ) ≤ 6501 := by
  decide

@[simp] lemma sigma_bound_1807 : (ArithmeticFunction.sigma 1 1807 : ℕ) ≤ 6505 := by
  decide

@[simp] lemma sigma_bound_1808 : (ArithmeticFunction.sigma 1 1808 : ℕ) ≤ 6508 := by
  decide

@[simp] lemma sigma_bound_1809 : (ArithmeticFunction.sigma 1 1809 : ℕ) ≤ 6512 := by
  decide

@[simp] lemma sigma_bound_1810 : (ArithmeticFunction.sigma 1 1810 : ℕ) ≤ 6516 := by
  decide

@[simp] lemma sigma_bound_1811 : (ArithmeticFunction.sigma 1 1811 : ℕ) ≤ 6519 := by
  decide

@[simp] lemma sigma_bound_1812 : (ArithmeticFunction.sigma 1 1812 : ℕ) ≤ 6523 := by
  decide

@[simp] lemma sigma_bound_1813 : (ArithmeticFunction.sigma 1 1813 : ℕ) ≤ 6526 := by
  decide

@[simp] lemma sigma_bound_1814 : (ArithmeticFunction.sigma 1 1814 : ℕ) ≤ 6530 := by
  decide

@[simp] lemma sigma_bound_1815 : (ArithmeticFunction.sigma 1 1815 : ℕ) ≤ 6534 := by
  decide

@[simp] lemma sigma_bound_1816 : (ArithmeticFunction.sigma 1 1816 : ℕ) ≤ 6537 := by
  decide

@[simp] lemma sigma_bound_1817 : (ArithmeticFunction.sigma 1 1817 : ℕ) ≤ 6541 := by
  decide

@[simp] lemma sigma_bound_1818 : (ArithmeticFunction.sigma 1 1818 : ℕ) ≤ 6544 := by
  decide

@[simp] lemma sigma_bound_1819 : (ArithmeticFunction.sigma 1 1819 : ℕ) ≤ 6548 := by
  decide

@[simp] lemma sigma_bound_1820 : (ArithmeticFunction.sigma 1 1820 : ℕ) ≤ 6552 := by
  decide

@[simp] lemma sigma_bound_1821 : (ArithmeticFunction.sigma 1 1821 : ℕ) ≤ 6555 := by
  decide

@[simp] lemma sigma_bound_1822 : (ArithmeticFunction.sigma 1 1822 : ℕ) ≤ 6559 := by
  decide

@[simp] lemma sigma_bound_1823 : (ArithmeticFunction.sigma 1 1823 : ℕ) ≤ 6562 := by
  decide

@[simp] lemma sigma_bound_1824 : (ArithmeticFunction.sigma 1 1824 : ℕ) ≤ 6566 := by
  decide

@[simp] lemma sigma_bound_1825 : (ArithmeticFunction.sigma 1 1825 : ℕ) ≤ 6570 := by
  decide

@[simp] lemma sigma_bound_1826 : (ArithmeticFunction.sigma 1 1826 : ℕ) ≤ 6573 := by
  decide

@[simp] lemma sigma_bound_1827 : (ArithmeticFunction.sigma 1 1827 : ℕ) ≤ 6577 := by
  decide

@[simp] lemma sigma_bound_1828 : (ArithmeticFunction.sigma 1 1828 : ℕ) ≤ 6580 := by
  decide

@[simp] lemma sigma_bound_1829 : (ArithmeticFunction.sigma 1 1829 : ℕ) ≤ 6584 := by
  decide

@[simp] lemma sigma_bound_1830 : (ArithmeticFunction.sigma 1 1830 : ℕ) ≤ 6588 := by
  decide

@[simp] lemma sigma_bound_1831 : (ArithmeticFunction.sigma 1 1831 : ℕ) ≤ 6591 := by
  decide

@[simp] lemma sigma_bound_1832 : (ArithmeticFunction.sigma 1 1832 : ℕ) ≤ 6595 := by
  decide

@[simp] lemma sigma_bound_1833 : (ArithmeticFunction.sigma 1 1833 : ℕ) ≤ 6598 := by
  decide

@[simp] lemma sigma_bound_1834 : (ArithmeticFunction.sigma 1 1834 : ℕ) ≤ 6602 := by
  decide

@[simp] lemma sigma_bound_1835 : (ArithmeticFunction.sigma 1 1835 : ℕ) ≤ 6606 := by
  decide

@[simp] lemma sigma_bound_1836 : (ArithmeticFunction.sigma 1 1836 : ℕ) ≤ 6609 := by
  decide

@[simp] lemma sigma_bound_1837 : (ArithmeticFunction.sigma 1 1837 : ℕ) ≤ 6613 := by
  decide

@[simp] lemma sigma_bound_1838 : (ArithmeticFunction.sigma 1 1838 : ℕ) ≤ 6616 := by
  decide

@[simp] lemma sigma_bound_1839 : (ArithmeticFunction.sigma 1 1839 : ℕ) ≤ 6620 := by
  decide

@[simp] lemma sigma_bound_1840 : (ArithmeticFunction.sigma 1 1840 : ℕ) ≤ 6624 := by
  decide

@[simp] lemma sigma_bound_1841 : (ArithmeticFunction.sigma 1 1841 : ℕ) ≤ 6627 := by
  decide

@[simp] lemma sigma_bound_1842 : (ArithmeticFunction.sigma 1 1842 : ℕ) ≤ 6631 := by
  decide

@[simp] lemma sigma_bound_1843 : (ArithmeticFunction.sigma 1 1843 : ℕ) ≤ 6634 := by
  decide

@[simp] lemma sigma_bound_1844 : (ArithmeticFunction.sigma 1 1844 : ℕ) ≤ 6638 := by
  decide

@[simp] lemma sigma_bound_1845 : (ArithmeticFunction.sigma 1 1845 : ℕ) ≤ 6642 := by
  decide

@[simp] lemma sigma_bound_1846 : (ArithmeticFunction.sigma 1 1846 : ℕ) ≤ 6645 := by
  decide

@[simp] lemma sigma_bound_1847 : (ArithmeticFunction.sigma 1 1847 : ℕ) ≤ 6649 := by
  decide

@[simp] lemma sigma_bound_1848 : (ArithmeticFunction.sigma 1 1848 : ℕ) ≤ 6652 := by
  decide

@[simp] lemma sigma_bound_1849 : (ArithmeticFunction.sigma 1 1849 : ℕ) ≤ 6656 := by
  decide

@[simp] lemma sigma_bound_1850 : (ArithmeticFunction.sigma 1 1850 : ℕ) ≤ 6660 := by
  decide

@[simp] lemma sigma_bound_1851 : (ArithmeticFunction.sigma 1 1851 : ℕ) ≤ 6663 := by
  decide

@[simp] lemma sigma_bound_1852 : (ArithmeticFunction.sigma 1 1852 : ℕ) ≤ 6667 := by
  decide

@[simp] lemma sigma_bound_1853 : (ArithmeticFunction.sigma 1 1853 : ℕ) ≤ 6670 := by
  decide

@[simp] lemma sigma_bound_1854 : (ArithmeticFunction.sigma 1 1854 : ℕ) ≤ 6674 := by
  decide

@[simp] lemma sigma_bound_1855 : (ArithmeticFunction.sigma 1 1855 : ℕ) ≤ 6678 := by
  decide

@[simp] lemma sigma_bound_1856 : (ArithmeticFunction.sigma 1 1856 : ℕ) ≤ 6681 := by
  decide

@[simp] lemma sigma_bound_1857 : (ArithmeticFunction.sigma 1 1857 : ℕ) ≤ 6685 := by
  decide

@[simp] lemma sigma_bound_1858 : (ArithmeticFunction.sigma 1 1858 : ℕ) ≤ 6688 := by
  decide

@[simp] lemma sigma_bound_1859 : (ArithmeticFunction.sigma 1 1859 : ℕ) ≤ 6692 := by
  decide

@[simp] lemma sigma_bound_1860 : (ArithmeticFunction.sigma 1 1860 : ℕ) ≤ 6696 := by
  decide

@[simp] lemma sigma_bound_1861 : (ArithmeticFunction.sigma 1 1861 : ℕ) ≤ 6699 := by
  decide

@[simp] lemma sigma_bound_1862 : (ArithmeticFunction.sigma 1 1862 : ℕ) ≤ 6703 := by
  decide

@[simp] lemma sigma_bound_1863 : (ArithmeticFunction.sigma 1 1863 : ℕ) ≤ 6706 := by
  decide

@[simp] lemma sigma_bound_1864 : (ArithmeticFunction.sigma 1 1864 : ℕ) ≤ 6710 := by
  decide

@[simp] lemma sigma_bound_1865 : (ArithmeticFunction.sigma 1 1865 : ℕ) ≤ 6714 := by
  decide

@[simp] lemma sigma_bound_1866 : (ArithmeticFunction.sigma 1 1866 : ℕ) ≤ 6717 := by
  decide

@[simp] lemma sigma_bound_1867 : (ArithmeticFunction.sigma 1 1867 : ℕ) ≤ 6721 := by
  decide

@[simp] lemma sigma_bound_1868 : (ArithmeticFunction.sigma 1 1868 : ℕ) ≤ 6724 := by
  decide

@[simp] lemma sigma_bound_1869 : (ArithmeticFunction.sigma 1 1869 : ℕ) ≤ 6728 := by
  decide

@[simp] lemma sigma_bound_1870 : (ArithmeticFunction.sigma 1 1870 : ℕ) ≤ 6732 := by
  decide

@[simp] lemma sigma_bound_1871 : (ArithmeticFunction.sigma 1 1871 : ℕ) ≤ 6735 := by
  decide

@[simp] lemma sigma_bound_1872 : (ArithmeticFunction.sigma 1 1872 : ℕ) ≤ 6739 := by
  decide

@[simp] lemma sigma_bound_1873 : (ArithmeticFunction.sigma 1 1873 : ℕ) ≤ 6742 := by
  decide

@[simp] lemma sigma_bound_1874 : (ArithmeticFunction.sigma 1 1874 : ℕ) ≤ 6746 := by
  decide

@[simp] lemma sigma_bound_1875 : (ArithmeticFunction.sigma 1 1875 : ℕ) ≤ 6750 := by
  decide

@[simp] lemma sigma_bound_1876 : (ArithmeticFunction.sigma 1 1876 : ℕ) ≤ 6753 := by
  decide

@[simp] lemma sigma_bound_1877 : (ArithmeticFunction.sigma 1 1877 : ℕ) ≤ 6757 := by
  decide

@[simp] lemma sigma_bound_1878 : (ArithmeticFunction.sigma 1 1878 : ℕ) ≤ 6760 := by
  decide

@[simp] lemma sigma_bound_1879 : (ArithmeticFunction.sigma 1 1879 : ℕ) ≤ 6764 := by
  decide

@[simp] lemma sigma_bound_1880 : (ArithmeticFunction.sigma 1 1880 : ℕ) ≤ 6768 := by
  decide

@[simp] lemma sigma_bound_1881 : (ArithmeticFunction.sigma 1 1881 : ℕ) ≤ 6771 := by
  decide

@[simp] lemma sigma_bound_1882 : (ArithmeticFunction.sigma 1 1882 : ℕ) ≤ 6775 := by
  decide

@[simp] lemma sigma_bound_1883 : (ArithmeticFunction.sigma 1 1883 : ℕ) ≤ 6778 := by
  decide

@[simp] lemma sigma_bound_1884 : (ArithmeticFunction.sigma 1 1884 : ℕ) ≤ 6782 := by
  decide

@[simp] lemma sigma_bound_1885 : (ArithmeticFunction.sigma 1 1885 : ℕ) ≤ 6786 := by
  decide

@[simp] lemma sigma_bound_1886 : (ArithmeticFunction.sigma 1 1886 : ℕ) ≤ 6789 := by
  decide

@[simp] lemma sigma_bound_1887 : (ArithmeticFunction.sigma 1 1887 : ℕ) ≤ 6793 := by
  decide

@[simp] lemma sigma_bound_1888 : (ArithmeticFunction.sigma 1 1888 : ℕ) ≤ 6796 := by
  decide

@[simp] lemma sigma_bound_1889 : (ArithmeticFunction.sigma 1 1889 : ℕ) ≤ 6800 := by
  decide

@[simp] lemma sigma_bound_1890 : (ArithmeticFunction.sigma 1 1890 : ℕ) ≤ 6804 := by
  decide

@[simp] lemma sigma_bound_1891 : (ArithmeticFunction.sigma 1 1891 : ℕ) ≤ 6807 := by
  decide

@[simp] lemma sigma_bound_1892 : (ArithmeticFunction.sigma 1 1892 : ℕ) ≤ 6811 := by
  decide

@[simp] lemma sigma_bound_1893 : (ArithmeticFunction.sigma 1 1893 : ℕ) ≤ 6814 := by
  decide

@[simp] lemma sigma_bound_1894 : (ArithmeticFunction.sigma 1 1894 : ℕ) ≤ 6818 := by
  decide

@[simp] lemma sigma_bound_1895 : (ArithmeticFunction.sigma 1 1895 : ℕ) ≤ 6822 := by
  decide

@[simp] lemma sigma_bound_1896 : (ArithmeticFunction.sigma 1 1896 : ℕ) ≤ 6825 := by
  decide

@[simp] lemma sigma_bound_1897 : (ArithmeticFunction.sigma 1 1897 : ℕ) ≤ 6829 := by
  decide

@[simp] lemma sigma_bound_1898 : (ArithmeticFunction.sigma 1 1898 : ℕ) ≤ 6832 := by
  decide

@[simp] lemma sigma_bound_1899 : (ArithmeticFunction.sigma 1 1899 : ℕ) ≤ 6836 := by
  decide

@[simp] lemma sigma_bound_1900 : (ArithmeticFunction.sigma 1 1900 : ℕ) ≤ 6840 := by
  decide

@[simp] lemma sigma_bound_1901 : (ArithmeticFunction.sigma 1 1901 : ℕ) ≤ 6843 := by
  decide

@[simp] lemma sigma_bound_1902 : (ArithmeticFunction.sigma 1 1902 : ℕ) ≤ 6847 := by
  decide

@[simp] lemma sigma_bound_1903 : (ArithmeticFunction.sigma 1 1903 : ℕ) ≤ 6850 := by
  decide

@[simp] lemma sigma_bound_1904 : (ArithmeticFunction.sigma 1 1904 : ℕ) ≤ 6854 := by
  decide

@[simp] lemma sigma_bound_1905 : (ArithmeticFunction.sigma 1 1905 : ℕ) ≤ 6858 := by
  decide

@[simp] lemma sigma_bound_1906 : (ArithmeticFunction.sigma 1 1906 : ℕ) ≤ 6861 := by
  decide

@[simp] lemma sigma_bound_1907 : (ArithmeticFunction.sigma 1 1907 : ℕ) ≤ 6865 := by
  decide

@[simp] lemma sigma_bound_1908 : (ArithmeticFunction.sigma 1 1908 : ℕ) ≤ 6868 := by
  decide

@[simp] lemma sigma_bound_1909 : (ArithmeticFunction.sigma 1 1909 : ℕ) ≤ 6872 := by
  decide

@[simp] lemma sigma_bound_1910 : (ArithmeticFunction.sigma 1 1910 : ℕ) ≤ 6876 := by
  decide

@[simp] lemma sigma_bound_1911 : (ArithmeticFunction.sigma 1 1911 : ℕ) ≤ 6879 := by
  decide

@[simp] lemma sigma_bound_1912 : (ArithmeticFunction.sigma 1 1912 : ℕ) ≤ 6883 := by
  decide

@[simp] lemma sigma_bound_1913 : (ArithmeticFunction.sigma 1 1913 : ℕ) ≤ 6886 := by
  decide

@[simp] lemma sigma_bound_1914 : (ArithmeticFunction.sigma 1 1914 : ℕ) ≤ 6890 := by
  decide

@[simp] lemma sigma_bound_1915 : (ArithmeticFunction.sigma 1 1915 : ℕ) ≤ 6894 := by
  decide

@[simp] lemma sigma_bound_1916 : (ArithmeticFunction.sigma 1 1916 : ℕ) ≤ 6897 := by
  decide

@[simp] lemma sigma_bound_1917 : (ArithmeticFunction.sigma 1 1917 : ℕ) ≤ 6901 := by
  decide

@[simp] lemma sigma_bound_1918 : (ArithmeticFunction.sigma 1 1918 : ℕ) ≤ 6904 := by
  decide

@[simp] lemma sigma_bound_1919 : (ArithmeticFunction.sigma 1 1919 : ℕ) ≤ 6908 := by
  decide

@[simp] lemma sigma_bound_1920 : (ArithmeticFunction.sigma 1 1920 : ℕ) ≤ 6912 := by
  decide

@[simp] lemma sigma_bound_1921 : (ArithmeticFunction.sigma 1 1921 : ℕ) ≤ 6915 := by
  decide

@[simp] lemma sigma_bound_1922 : (ArithmeticFunction.sigma 1 1922 : ℕ) ≤ 6919 := by
  decide

@[simp] lemma sigma_bound_1923 : (ArithmeticFunction.sigma 1 1923 : ℕ) ≤ 6922 := by
  decide

@[simp] lemma sigma_bound_1924 : (ArithmeticFunction.sigma 1 1924 : ℕ) ≤ 6926 := by
  decide

@[simp] lemma sigma_bound_1925 : (ArithmeticFunction.sigma 1 1925 : ℕ) ≤ 6930 := by
  decide

@[simp] lemma sigma_bound_1926 : (ArithmeticFunction.sigma 1 1926 : ℕ) ≤ 6933 := by
  decide

@[simp] lemma sigma_bound_1927 : (ArithmeticFunction.sigma 1 1927 : ℕ) ≤ 6937 := by
  decide

@[simp] lemma sigma_bound_1928 : (ArithmeticFunction.sigma 1 1928 : ℕ) ≤ 6940 := by
  decide

@[simp] lemma sigma_bound_1929 : (ArithmeticFunction.sigma 1 1929 : ℕ) ≤ 6944 := by
  decide

@[simp] lemma sigma_bound_1930 : (ArithmeticFunction.sigma 1 1930 : ℕ) ≤ 6948 := by
  decide

@[simp] lemma sigma_bound_1931 : (ArithmeticFunction.sigma 1 1931 : ℕ) ≤ 6951 := by
  decide

@[simp] lemma sigma_bound_1932 : (ArithmeticFunction.sigma 1 1932 : ℕ) ≤ 6955 := by
  decide

@[simp] lemma sigma_bound_1933 : (ArithmeticFunction.sigma 1 1933 : ℕ) ≤ 6958 := by
  decide

@[simp] lemma sigma_bound_1934 : (ArithmeticFunction.sigma 1 1934 : ℕ) ≤ 6962 := by
  decide

@[simp] lemma sigma_bound_1935 : (ArithmeticFunction.sigma 1 1935 : ℕ) ≤ 6966 := by
  decide

@[simp] lemma sigma_bound_1936 : (ArithmeticFunction.sigma 1 1936 : ℕ) ≤ 6969 := by
  decide

@[simp] lemma sigma_bound_1937 : (ArithmeticFunction.sigma 1 1937 : ℕ) ≤ 6973 := by
  decide

@[simp] lemma sigma_bound_1938 : (ArithmeticFunction.sigma 1 1938 : ℕ) ≤ 6976 := by
  decide

@[simp] lemma sigma_bound_1939 : (ArithmeticFunction.sigma 1 1939 : ℕ) ≤ 6980 := by
  decide

@[simp] lemma sigma_bound_1940 : (ArithmeticFunction.sigma 1 1940 : ℕ) ≤ 6984 := by
  decide

@[simp] lemma sigma_bound_1941 : (ArithmeticFunction.sigma 1 1941 : ℕ) ≤ 6987 := by
  decide

@[simp] lemma sigma_bound_1942 : (ArithmeticFunction.sigma 1 1942 : ℕ) ≤ 6991 := by
  decide

@[simp] lemma sigma_bound_1943 : (ArithmeticFunction.sigma 1 1943 : ℕ) ≤ 6994 := by
  decide

@[simp] lemma sigma_bound_1944 : (ArithmeticFunction.sigma 1 1944 : ℕ) ≤ 6998 := by
  decide

@[simp] lemma sigma_bound_1945 : (ArithmeticFunction.sigma 1 1945 : ℕ) ≤ 7002 := by
  decide

@[simp] lemma sigma_bound_1946 : (ArithmeticFunction.sigma 1 1946 : ℕ) ≤ 7005 := by
  decide

@[simp] lemma sigma_bound_1947 : (ArithmeticFunction.sigma 1 1947 : ℕ) ≤ 7009 := by
  decide

@[simp] lemma sigma_bound_1948 : (ArithmeticFunction.sigma 1 1948 : ℕ) ≤ 7012 := by
  decide

@[simp] lemma sigma_bound_1949 : (ArithmeticFunction.sigma 1 1949 : ℕ) ≤ 7016 := by
  decide

@[simp] lemma sigma_bound_1950 : (ArithmeticFunction.sigma 1 1950 : ℕ) ≤ 7020 := by
  decide

@[simp] lemma sigma_bound_1951 : (ArithmeticFunction.sigma 1 1951 : ℕ) ≤ 7023 := by
  decide

@[simp] lemma sigma_bound_1952 : (ArithmeticFunction.sigma 1 1952 : ℕ) ≤ 7027 := by
  decide

@[simp] lemma sigma_bound_1953 : (ArithmeticFunction.sigma 1 1953 : ℕ) ≤ 7030 := by
  decide

@[simp] lemma sigma_bound_1954 : (ArithmeticFunction.sigma 1 1954 : ℕ) ≤ 7034 := by
  decide

@[simp] lemma sigma_bound_1955 : (ArithmeticFunction.sigma 1 1955 : ℕ) ≤ 7038 := by
  decide

@[simp] lemma sigma_bound_1956 : (ArithmeticFunction.sigma 1 1956 : ℕ) ≤ 7041 := by
  decide

@[simp] lemma sigma_bound_1957 : (ArithmeticFunction.sigma 1 1957 : ℕ) ≤ 7045 := by
  decide

@[simp] lemma sigma_bound_1958 : (ArithmeticFunction.sigma 1 1958 : ℕ) ≤ 7048 := by
  decide

@[simp] lemma sigma_bound_1959 : (ArithmeticFunction.sigma 1 1959 : ℕ) ≤ 7052 := by
  decide

@[simp] lemma sigma_bound_1960 : (ArithmeticFunction.sigma 1 1960 : ℕ) ≤ 7056 := by
  decide

@[simp] lemma sigma_bound_1961 : (ArithmeticFunction.sigma 1 1961 : ℕ) ≤ 7059 := by
  decide

@[simp] lemma sigma_bound_1962 : (ArithmeticFunction.sigma 1 1962 : ℕ) ≤ 7063 := by
  decide

@[simp] lemma sigma_bound_1963 : (ArithmeticFunction.sigma 1 1963 : ℕ) ≤ 7066 := by
  decide

@[simp] lemma sigma_bound_1964 : (ArithmeticFunction.sigma 1 1964 : ℕ) ≤ 7070 := by
  decide

@[simp] lemma sigma_bound_1965 : (ArithmeticFunction.sigma 1 1965 : ℕ) ≤ 7074 := by
  decide

@[simp] lemma sigma_bound_1966 : (ArithmeticFunction.sigma 1 1966 : ℕ) ≤ 7077 := by
  decide

@[simp] lemma sigma_bound_1967 : (ArithmeticFunction.sigma 1 1967 : ℕ) ≤ 7081 := by
  decide

@[simp] lemma sigma_bound_1968 : (ArithmeticFunction.sigma 1 1968 : ℕ) ≤ 7084 := by
  decide

@[simp] lemma sigma_bound_1969 : (ArithmeticFunction.sigma 1 1969 : ℕ) ≤ 7088 := by
  decide

@[simp] lemma sigma_bound_1970 : (ArithmeticFunction.sigma 1 1970 : ℕ) ≤ 7092 := by
  decide

@[simp] lemma sigma_bound_1971 : (ArithmeticFunction.sigma 1 1971 : ℕ) ≤ 7095 := by
  decide

@[simp] lemma sigma_bound_1972 : (ArithmeticFunction.sigma 1 1972 : ℕ) ≤ 7099 := by
  decide

@[simp] lemma sigma_bound_1973 : (ArithmeticFunction.sigma 1 1973 : ℕ) ≤ 7102 := by
  decide

@[simp] lemma sigma_bound_1974 : (ArithmeticFunction.sigma 1 1974 : ℕ) ≤ 7106 := by
  decide

@[simp] lemma sigma_bound_1975 : (ArithmeticFunction.sigma 1 1975 : ℕ) ≤ 7110 := by
  decide

@[simp] lemma sigma_bound_1976 : (ArithmeticFunction.sigma 1 1976 : ℕ) ≤ 7113 := by
  decide

@[simp] lemma sigma_bound_1977 : (ArithmeticFunction.sigma 1 1977 : ℕ) ≤ 7117 := by
  decide

@[simp] lemma sigma_bound_1978 : (ArithmeticFunction.sigma 1 1978 : ℕ) ≤ 7120 := by
  decide

@[simp] lemma sigma_bound_1979 : (ArithmeticFunction.sigma 1 1979 : ℕ) ≤ 7124 := by
  decide

@[simp] lemma sigma_bound_1980 : (ArithmeticFunction.sigma 1 1980 : ℕ) ≤ 7128 := by
  decide

@[simp] lemma sigma_bound_1981 : (ArithmeticFunction.sigma 1 1981 : ℕ) ≤ 7131 := by
  decide

@[simp] lemma sigma_bound_1982 : (ArithmeticFunction.sigma 1 1982 : ℕ) ≤ 7135 := by
  decide

@[simp] lemma sigma_bound_1983 : (ArithmeticFunction.sigma 1 1983 : ℕ) ≤ 7138 := by
  decide

@[simp] lemma sigma_bound_1984 : (ArithmeticFunction.sigma 1 1984 : ℕ) ≤ 7142 := by
  decide

@[simp] lemma sigma_bound_1985 : (ArithmeticFunction.sigma 1 1985 : ℕ) ≤ 7146 := by
  decide

@[simp] lemma sigma_bound_1986 : (ArithmeticFunction.sigma 1 1986 : ℕ) ≤ 7149 := by
  decide

@[simp] lemma sigma_bound_1987 : (ArithmeticFunction.sigma 1 1987 : ℕ) ≤ 7153 := by
  decide

@[simp] lemma sigma_bound_1988 : (ArithmeticFunction.sigma 1 1988 : ℕ) ≤ 7156 := by
  decide

@[simp] lemma sigma_bound_1989 : (ArithmeticFunction.sigma 1 1989 : ℕ) ≤ 7160 := by
  decide

@[simp] lemma sigma_bound_1990 : (ArithmeticFunction.sigma 1 1990 : ℕ) ≤ 7164 := by
  decide

@[simp] lemma sigma_bound_1991 : (ArithmeticFunction.sigma 1 1991 : ℕ) ≤ 7167 := by
  decide

@[simp] lemma sigma_bound_1992 : (ArithmeticFunction.sigma 1 1992 : ℕ) ≤ 7171 := by
  decide

@[simp] lemma sigma_bound_1993 : (ArithmeticFunction.sigma 1 1993 : ℕ) ≤ 7174 := by
  decide

@[simp] lemma sigma_bound_1994 : (ArithmeticFunction.sigma 1 1994 : ℕ) ≤ 7178 := by
  decide

@[simp] lemma sigma_bound_1995 : (ArithmeticFunction.sigma 1 1995 : ℕ) ≤ 7182 := by
  decide

@[simp] lemma sigma_bound_1996 : (ArithmeticFunction.sigma 1 1996 : ℕ) ≤ 7185 := by
  decide

@[simp] lemma sigma_bound_1997 : (ArithmeticFunction.sigma 1 1997 : ℕ) ≤ 7189 := by
  decide

@[simp] lemma sigma_bound_1998 : (ArithmeticFunction.sigma 1 1998 : ℕ) ≤ 7192 := by
  decide

@[simp] lemma sigma_bound_1999 : (ArithmeticFunction.sigma 1 1999 : ℕ) ≤ 7196 := by
  decide

@[simp] lemma sigma_bound_2000 : (ArithmeticFunction.sigma 1 2000 : ℕ) ≤ 7200 := by
  decide


lemma sigma_le_18_5_range (n : ℕ) (hL : 1501 ≤ n) (hU : n ≤ 2000) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 18 * n / 5 := by
  interval_cases n <;> simp


/-!  Explicit lower bounds for a few real exponential and logarithmic constants. -/

lemma exp_57_100_ge : (44 / 25 : ℝ) ≤ Real.exp (57 / 100) := by
  have hsum_ge : (44 / 25 : ℝ) ≤
      ∑ i ∈ Finset.range 5, (57 / 100 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num
  have hsum_le_exp := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (57 / 100 : ℝ)) 5
  linarith

lemma exp_1_20_upper : Real.exp (1 / 20) ≤ 645901 / 614400 := by
  have h := Real.exp_bound' (x := (1 / 20 : ℝ)) (n := 4) (by norm_num : 0 ≤ (1 / 20 : ℝ))
    (by norm_num : (1 / 20 : ℝ) ≤ 1) (by norm_num : 0 < 4)
  norm_num at h
  simpa using h

lemma exp_41_20_le_777_100 : Real.exp (41 / 20) ≤ 777 / 100 := by
  have h1 := Real.exp_one_lt_d9
  have hpos : 0 ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
  have hexp2 : Real.exp 2 < (2.7182818286 : ℝ) ^ 2 := by
    have hpow := pow_lt_pow_left₀ h1 hpos (by norm_num : (2 : ℕ) ≠ 0)
    simpa [Real.exp_one_pow] using hpow
  have h02 := exp_1_20_upper
  have h02pos : 0 < Real.exp (1 / 20) := Real.exp_pos _
  have hmul : Real.exp 2 * Real.exp (1 / 20) <
      (2.7182818286 : ℝ) ^ 2 * (645901 / 614400) := by
    exact mul_lt_mul hexp2 h02 h02pos (by positivity)
  have hmain : Real.exp (41 / 20) < (2.7182818286 : ℝ) ^ 2 * (645901 / 614400) := by
    have hsum : (41 / 20 : ℝ) = 2 + 1 / 20 := by norm_num
    rw [hsum, Real.exp_add]
    exact hmul
  have hbound : (2.7182818286 : ℝ) ^ 2 * (645901 / 614400) ≤ 777 / 100 := by norm_num
  exact hmain.le.trans hbound

lemma exp_36_5_le_1502 : Real.exp (36 / 5) ≤ 1502 := by
  have h1 := Real.exp_one_lt_d9
  have hpos : 0 ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
  have h7 : Real.exp 7 < (2.7182818286 : ℝ) ^ 7 := by
    have hpow := pow_lt_pow_left₀ h1 hpos (by norm_num : (7 : ℕ) ≠ 0)
    simpa [Real.exp_one_pow] using hpow
  have h02 : Real.exp (1 / 5) ≤ 5 / 4 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : 0 ≤ (1/5:ℝ)) (by norm_num : (1/5:ℝ) < 1)
    norm_num at h
    simpa using h
  have h02pos : 0 < Real.exp (1 / 5) := Real.exp_pos _
  have hmul : Real.exp 7 * Real.exp (1 / 5) < (2.7182818286 : ℝ) ^ 7 * (5 / 4) := by
    exact mul_lt_mul h7 h02 h02pos (by positivity)
  have hmain : Real.exp (36 / 5) < (2.7182818286 : ℝ) ^ 7 * (5 / 4) := by
    have hsum : (36 / 5 : ℝ) = 7 + 1 / 5 := by norm_num
    rw [hsum, Real.exp_add]
    exact hmul
  have hbound : (2.7182818286 : ℝ) ^ 7 * (5 / 4) ≤ 1502 := by norm_num
  exact hmain.le.trans hbound

lemma log_1502_ge_36_5 : 36 / 5 ≤ Real.log 1502 := by
  have hpos : 0 < (1502 : ℝ) := by norm_num
  exact (Real.le_log_iff_exp_le hpos).2 exp_36_5_le_1502

lemma exp_4616_1000_ge_101 : (101 : ℝ) ≤ Real.exp (4616 / 1000) := by
  have hsum_ge : (101 : ℝ) ≤
      ∑ i ∈ Finset.range 14, (4616 / 1000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num
  have hsum_le_exp := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (4616 / 1000 : ℝ)) 14
  linarith

lemma log_101_le_4616_1000 : Real.log 101 ≤ 4616 / 1000 := by
  have hpos : 0 < (101 : ℝ) := by norm_num
  exact (Real.log_le_iff_le_exp hpos).2 exp_4616_1000_ge_101

/-!  A lower bound for the harmonic numbers in the finite range. -/

lemma harmonic_ge_log_add_57_100 (n : ℕ) (hn : 100 ≤ n) :
    (57 / 100 : ℝ) + Real.log (n + 1) ≤ harmonic n := by
  have hH100 : (5186 / 1000 : ℝ) ≤ harmonic 100 := by
    norm_num [harmonic]
  have hlog101 : Real.log 101 ≤ 4616 / 1000 := log_101_le_4616_1000
  have hseq100 : (57 / 100 : ℝ) ≤ Real.eulerMascheroniSeq 100 := by
    unfold Real.eulerMascheroniSeq
    norm_num [hlog101]
    linarith
  have hmono := Real.strictMono_eulerMascheroniSeq.monotone hn
  have hseqn : (57 / 100 : ℝ) ≤ Real.eulerMascheroniSeq n := hseq100.trans hmono
  unfold Real.eulerMascheroniSeq at hseqn
  linarith

lemma log_n_add_one_ge_36_5 (n : ℕ) (hL : 1501 ≤ n) :
    36 / 5 ≤ Real.log (n + 1) := by
  have hsucc : 1502 ≤ n + 1 := by omega
  have hle : Real.log 1502 ≤ Real.log (n + 1) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hsucc)
  linarith [log_1502_ge_36_5, hle]

/-!  The right-hand side dominates `18/5 * n` on the finite range. -/

lemma rhs_ge_18_5_mul (n : ℕ) (hL : 1501 ≤ n) :
    (18 : ℝ) * n / 5 ≤ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hn100 : 100 ≤ n := by linarith
  have hH : (57 / 100 : ℝ) + Real.log (n + 1) ≤ (harmonic n : ℝ) := by
    exact_mod_cast harmonic_ge_log_add_57_100 n hn100
  let x0 : ℝ := (57 / 100 : ℝ) + Real.log (n + 1)
  have hx0_le_H : x0 ≤ (harmonic n : ℝ) := by
    dsimp [x0]; exact hH
  have hlog_n := log_n_add_one_ge_36_5 n hL
  have hx0_pos : 0 < x0 := by
    dsimp [x0]
    linarith
  have hx0_gt_one : 1 < x0 := by
    dsimp [x0]
    linarith
  have hexp_mono : Real.exp x0 ≤ Real.exp (harmonic n : ℝ) := by
    exact Real.exp_le_exp.mpr hx0_le_H
  have hlog_mono : Real.log x0 ≤ Real.log (harmonic n : ℝ) := by
    exact Real.log_le_log hx0_pos hx0_le_H
  have hprod : Real.exp x0 * Real.log x0 ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
    exact mul_le_mul hexp_mono hlog_mono (Real.log_nonneg (le_of_lt hx0_gt_one)) (le_of_lt (Real.exp_pos _))
  have hprod_ge : (18 : ℝ) * n / 5 ≤ Real.exp x0 * Real.log x0 := by
    have hlogx : 41 / 20 ≤ Real.log x0 := by
      have hx0_ge : 777 / 100 ≤ x0 := by
        dsimp [x0]
        linarith
      have hexp_le_x0 : Real.exp (41 / 20) ≤ x0 := (exp_41_20_le_777_100).trans hx0_ge
      exact (Real.le_log_iff_exp_le hx0_pos).2 hexp_le_x0
    have hexp57 : 44 / 25 ≤ Real.exp (57 / 100) := exp_57_100_ge
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hnexp : (n + 1 : ℝ) * (44 / 25) ≤ Real.exp x0 := by
      have hcalc : Real.exp x0 = (n + 1 : ℝ) * Real.exp (57 / 100) := by
        dsimp [x0]
        rw [Real.exp_add, Real.exp_log hnpos]
        ring
      rw [hcalc]
      exact mul_le_mul_of_nonneg_left hexp57 (by positivity)
    have hprod' : ((n + 1 : ℝ) * (44 / 25)) * (41 / 20) ≤ Real.exp x0 * Real.log x0 := by
      exact mul_le_mul hnexp hlogx (by linarith) (le_of_lt (Real.exp_pos x0))
    have hfinal : (18 : ℝ) * n / 5 ≤ ((n + 1 : ℝ) * (44 / 25)) * (41 / 20) := by
      nlinarith
    exact hfinal.trans hprod'
  have hHnonneg : 0 ≤ (harmonic n : ℝ) := by
    nlinarith [hx0_pos, hx0_le_H]
  have hprod_rhs : Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
    exact le_add_of_nonneg_left hHnonneg
  exact hprod_ge.trans (hprod.trans hprod_rhs)

theorem finite_check_range_1501_2000 (n : ℕ) (hn0 : 0 < n) (hL : 1501 ≤ n) (hU : n ≤ 2000) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 18 * n / 5 :=
    sigma_le_18_5_range n hL hU
  have hsig_real : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ ((18 * n / 5 : ℕ) : ℝ) := by
    exact_mod_cast hsig_nat
  have hdiv_le' : ((18 * n / 5 : ℕ) : ℝ) ≤ ((18 * n : ℕ) : ℝ) / 5 := by
    exact Nat.cast_div_le (m := 18 * n) (n := 5)
  have hdiv_le : ((18 * n / 5 : ℕ) : ℝ) ≤ (18 : ℝ) * n / 5 := by
    have hrewrite : ((18 * n : ℕ) : ℝ) / 5 = (18 : ℝ) * n / 5 := by
      norm_num [Nat.cast_mul]
    linarith
  have hrhs : (18 : ℝ) * n / 5 ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) :=
    rhs_ge_18_5_mul n hL
  linarith

end Commons.NumberTheory.Lagarias